use std::{collections::{HashMap, HashSet}, iter};

use batsat::{intmap::AsIndex, lbool, BasicSolver, Lit, SolverInterface, Var};
use smol_str::SmolStr;

use crate::{ast::{Implementation, MethodTy, SpanNode, Type}, eval::EvalError};

fn rename_tv_names_helper(func: u64, mut method: MethodTy, idx: Option<usize>) -> MethodTy {
    for (i, ty) in method.params.iter_mut().chain(iter::once(&mut *method.ret)).enumerate() {
        match ty {
            Type::TypeVariable { id, implements } => {
                if let Some(implements) = implements {
                    for imp in implements.iter_mut() {
                        imp.method = rename_tv_names_helper(
                            func,
                            std::mem::replace(&mut imp.method, MethodTy {
                                params: vec![], ret: Box::new(Type::Unit)
                            }),
                            Some(i)
                        );
                    }
                }
                let id = if id == "_" {
                    format!("{func}__anon{}", idx.unwrap_or(i)).into()
                } else {
                    format!("{func}__{id}").into()
                };
                let implements = std::mem::replace(implements, None);
                let _ = std::mem::replace(
                    ty,
                    Type::TypeVariable { id, implements }
                );
            }
            _ => ()
        }
    }
    method
}
pub fn rename_tv_names(method: Type) -> Type {
    let method_id = *method.as_method().unwrap().1;
    Type::Method(
        rename_tv_names_helper(method_id, method.into_method().unwrap().0, None),
        method_id
    )
}

fn flatten_impls_helper(method: &MethodTy, dict: &mut HashMap<SmolStr, HashSet<Implementation>>) {
    for p in &method.params {
        if let Type::TypeVariable { id, implements } = p {
            dict.entry(id.clone())
                .or_insert_with(Default::default)
                .extend(implements.as_ref().map(|x| x.as_slice()).unwrap_or(&[]).iter().cloned());
            if let Some(implements) = implements {
                for imp in implements.iter() {
                    flatten_impls_helper(&imp.method, dict);
                }
            }
        }
    }
}
pub fn flatten_impls(method: &MethodTy) -> HashMap<SmolStr, HashSet<Implementation>> {
    let mut dict = HashMap::new();
    flatten_impls_helper(method, &mut dict);
    dict
}

/// Recursively build SAT constraints to select exactly one implementation of `name`
/// that takes as input the provided `call_tys`.
/// Returns a map of method vars to their Types, and a fresh `sat_var`
/// that is true iff some implementation holds.
fn add_match_constraints<T>(
    solver: &mut BasicSolver,
    type_variables: &mut HashMap<SmolStr, HashMap<Type, Var>>,
    type_variable_impls: &mut HashMap<SmolStr, HashSet<Implementation>>,
    name: &str,
    call_tys: &[Type],
    call_ret_ty: Option<&Type>,
    get_methods_by_name: &impl Fn(&str) -> Vec<(Type, T)>,
    inside_imp: bool
) -> (HashMap<Var, (Type, Option<T>)>, Var) {
    println!("{name} | {call_tys:?} {call_ret_ty:?}");
    // Gather candidate methods
    let methods = get_methods_by_name(name)
        .into_iter()
        // filter by arity
        .filter(|m| m.0.as_method().unwrap().0.params.len() == call_tys.len())
        //.map(|m| (rename_tv_names(m.0), m.1))
        .collect::<Vec<_>>();
    if methods.is_empty() {
        let sat_var = solver.new_var_default();
        solver.add_clause_reuse(&mut vec![Lit::new(sat_var, false)]);
        return (HashMap::new(), sat_var);
    }

    // Create a SAT var per candidate
    let mut method_vars: HashMap<Var, (Type, Option<T>)> = HashMap::new();
    for method in methods {
        let v = solver.new_var_default();
        method_vars.insert(v, (method.0, Some(method.1)));
    }

    let impls: Vec<Implementation> = call_tys.iter().filter_map(|ty| {
        match ty {
            Type::TypeVariable { implements: Some(implements), .. } => {
                Some(implements.iter().cloned().collect::<Vec<_>>())
            },
            _ => None
        }
    }).flat_map(|x| x).collect();
    for imp in impls {
        if imp.func == name {
            let v = solver.new_var_default();
            method_vars.insert(v, (Type::Method(imp.method, 0), None));
        }
    }

    // Link parameters
    for (&mvar, (method, _)) in &method_vars {
        println!("METHOD {method}");
        let MethodTy { params: param_tys, ret: ret_ty } = method.as_method().unwrap().0;
        let mut unify_pairs: Vec<(SmolStr, SmolStr)> = Vec::new();

        for (i, param_ty) in param_tys.iter().chain(iter::once(&**ret_ty)).enumerate() {
            // Allow dispatch on return type
            let actual = if i == call_tys.len() {
                if let Some(ref ret_ty) = call_ret_ty {
                    ret_ty
                } else {
                    // If we aren't provided a return type, skip it
                    continue;
                }
            } else {
                &call_tys[i]
            }; // The argument to the function

            match (param_ty, actual) {
                (Type::TypeVariable { id: type_var_name, implements }, concrete)
                if !matches!(concrete, Type::TypeVariable { .. })
                => {
                    println!("TVUS {type_var_name} = {concrete}");

                    // Bind the type variable to this concrete type under this method
                    let var_map = type_variables
                        .entry(type_var_name.clone())
                        .or_insert_with(HashMap::new);
                    let bind_var = var_map
                        .entry(concrete.clone())
                        .or_insert_with(|| solver.new_var_default());
                    // m -> binding_is_ty
                    solver.add_clause_reuse(&mut vec![
                        Lit::new(mvar, false),
                        Lit::new(*bind_var, true),
                    ]);

                    if let Type::TypeVariable { id, implements } = param_ty {
                        if let Some(implements) = implements {
                            let impl_map = type_variable_impls
                                .entry(type_var_name.clone())
                                .or_insert_with(Default::default);
                            impl_map.extend(implements.iter().cloned());
                        }

                        for imp in type_variable_impls.get(type_var_name).cloned().unwrap_or_default() {
                            println!("RECURSING {}", imp.func);
                            let nested = add_match_constraints(
                                solver,
                                type_variables,
                                type_variable_impls,
                                &imp.func,
                                &imp.method.params,
                                Some(&*imp.method.ret),
                                get_methods_by_name,
                                true
                            ).1;
                            // Require: if this method is chosen then nested must hold
                            solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(nested, true)]);
                        }
                    }
                },
                (concrete, Type::TypeVariable { id: type_var_name, implements })
                if !matches!(concrete, Type::TypeVariable { .. })
                => {
                    // Bind the type variable to this concrete type under this method
                    if inside_imp {
                        let var_map = type_variables
                            .entry(type_var_name.clone())
                            .or_insert_with(HashMap::new);
                        let bind_var = var_map
                            .entry(concrete.clone())
                            .or_insert_with(|| solver.new_var_default());
                        // m -> binding_is_ty
                        solver.add_clause_reuse(&mut vec![
                            Lit::new(mvar, false),
                            Lit::new(*bind_var, true),
                        ]);
                    } else {
                        // Don't bind unless in imp context
                        solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
                    }
                }
                (
                    Type::TypeVariable { id: type_var_lhs, implements: implements_lhs },
                    Type::TypeVariable { id: type_var_rhs, implements: implements_rhs }
                ) => {
                    // m -> unify lhs and rhs
                    if type_var_lhs != type_var_rhs {
                        unify_pairs.push((type_var_lhs.clone(), type_var_rhs.clone()));
                    }

                    if let Some(implements) = implements_lhs {
                        let impl_map = type_variable_impls
                            .entry(type_var_lhs.clone())
                            .or_insert_with(Default::default);
                        impl_map.extend(implements.iter().cloned());
                    }
                    if let Some(implements) = implements_rhs {
                        let impl_map = type_variable_impls
                            .entry(type_var_rhs.clone())
                            .or_insert_with(Default::default);
                        impl_map.extend(implements.iter().cloned());
                    }
                    
                    println!(" === {param_ty} vs. {actual}");
                    if inside_imp {
                        for imp in type_variable_impls.get(type_var_lhs).cloned().unwrap_or_default() {
                            println!("RECURSING {}", imp.func);
                            let nested = add_match_constraints(
                                solver,
                                type_variables,
                                type_variable_impls,
                                &imp.func,
                                &imp.method.params,
                                Some(&*imp.method.ret),
                                get_methods_by_name,
                                true
                            ).1;
                            // Require: if this method is chosen then nested must hold
                            solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(nested, true)]);
                        }
                        for imp in type_variable_impls.get(type_var_rhs).cloned().unwrap_or_default() {
                            println!("RECURSING {}", imp.func);
                            let nested = add_match_constraints(
                                solver,
                                type_variables,
                                type_variable_impls,
                                &imp.func,
                                &imp.method.params,
                                Some(&*imp.method.ret),
                                get_methods_by_name,
                                true
                            ).1;
                            // Require: if this method is chosen then nested must hold
                            solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(nested, true)]);
                        }
                    } else {
                        let lhs = Type::TypeVariable {
                            id: type_var_lhs.clone(),
                            implements: type_variable_impls.get(type_var_lhs).cloned().map(|x| x.into_iter().collect())
                        };
                        let rhs = Type::TypeVariable {
                            id: type_var_rhs.clone(),
                            implements: type_variable_impls.get(type_var_rhs).cloned().map(|x| x.into_iter().collect())
                        };
                        if !lhs.compatible(&rhs, false) {
                            // Exclude this method
                            solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
                            println!("EXCLUDED!!! {param_ty} vs. {actual}");
                        }
                    }
                }
                (lhs, rhs) => {
                    // Exclude mismatched concrete types
                    if !lhs.compatible(rhs, false) {
                        // Exclude this method
                        solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
                        println!("EXCLUDED!!! {lhs} vs. {rhs}");
                    }
                }
            }
        }

        // Unify all pairs under m
        println!("UNIFYING {unify_pairs:?}");
        // For each pair of TV
        for (lhs_id, rhs_id) in &unify_pairs {
            let mut lhs_map = type_variables.remove(lhs_id).unwrap_or(HashMap::new());
            let mut rhs_map = type_variables.remove(rhs_id).unwrap_or(HashMap::new());

            let mut all_tys: std::collections::HashSet<Type> = lhs_map.keys().cloned().collect();
            all_tys.extend(rhs_map.keys().cloned());

            // For all possible TV type assignments
            for ty in all_tys {
                println!(" - {ty}");
                let var_lhs = lhs_map.entry(ty.clone()).or_insert_with(|| solver.new_var_default());
                let var_rhs = rhs_map.entry(ty.clone()).or_insert_with(|| solver.new_var_default());
                // Enforce equivalence under mvar: var_lhs <-> var_rhs
                solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(*var_lhs, false), Lit::new(*var_rhs, true)]);
                solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(*var_rhs, false), Lit::new(*var_lhs, true)]);
            }

            type_variables.insert(lhs_id.clone(), lhs_map);
            type_variables.insert(rhs_id.clone(), rhs_map);
        }
    }

    // Exactly-one: OR(vars) and pairwise exclusion
    // solver.add_clause_reuse(
    //     &mut method_vars.keys().copied().map(|v| Lit::new(v, true)).collect()
    // );
    // let vars: Vec<Var> = method_vars.keys().copied().collect();
    // for i in 0..vars.len() {
    //     for j in (i+1)..vars.len() {
    //         solver.add_clause_reuse(&mut vec![Lit::new(vars[i], false), Lit::new(vars[j], false)]);
    //     }
    // }

    // SAT var for "some method holds"
    let sat_var = solver.new_var_default();
    // sat_var -> OR(method_vars)
    let mut or_clause = method_vars.keys().copied()
        .map(|v| Lit::new(v, true)).collect::<Vec<_>>();
    or_clause.push(Lit::new(sat_var, false));
    solver.add_clause_reuse(&mut or_clause);
    // each method_var -> sat_var
    for &v in method_vars.keys() {
        solver.add_clause_reuse(&mut vec![Lit::new(v, false), Lit::new(sat_var, true)]);
    }

    (method_vars, sat_var)
}

pub struct MethodResolution<T> {
    pub method_ty: Type,
    pub ret_ty: Type,
    pub data: Option<T>
}

pub fn resolve_method<T>(
    func: &SpanNode,
    call_tys: Vec<Type>,
    get_methods_by_name: impl Fn(&str) -> Vec<(Type, T)>
) -> Result<MethodResolution<T>, EvalError> {
    let func_name = func.as_symbol().unwrap();
    let mut solver = BasicSolver::default();
    let mut type_variables = HashMap::new();
    let mut type_variable_impls = HashMap::new();

    // let mut type_variable_impls = flatten_impls(&MethodTy {
    //     params: call_tys.clone(), ret: Box::new(Type::Unit)
    // });

    // Build constraints for `func` just like an `imp` resolution
    let (method_vars, sat) = add_match_constraints(
        &mut solver,
        &mut type_variables,
        &mut type_variable_impls,
        func_name,
        &call_tys,
        None,
        &get_methods_by_name,
        false
    );

    // XOR(type variable bindings)
    for tv_vars in type_variables.values().map(|v| v.values()).filter(|v| v.len() > 0) {
        solver.add_clause_reuse(
            &mut tv_vars.clone().copied().map(|v| Lit::new(v, true)).collect()
        );
        let vars: Vec<Var> = tv_vars.copied().collect();
        for i in 0..vars.len() {
            for j in (i+1)..vars.len() {
                solver.add_clause_reuse(&mut vec![Lit::new(vars[i], false), Lit::new(vars[j], false)]);
            }
        }
    }

    // Solve requiring that some method holds
    solver.solve_limited(&[Lit::new(sat, true)]);

    // Extract chosen method
    let (chosen_method_var, chosen_method_ty) =
        method_vars.into_iter().find(|(m, _)| solver.value_var(*m) == lbool::TRUE)
        .ok_or(EvalError::NoMethodMatches { span: func.tag.clone() })?;

    // Extract type variable assignments
    let mut concrete_type_variables = HashMap::new();
    println!("{type_variables:?}");
    for (tvname, tvmap) in type_variables {
        for (ty, tyvar) in tvmap {
            if solver.value_var(tyvar) == lbool::TRUE {
                if let Some(existing_ty) = concrete_type_variables.get(&tvname) {
                    assert_eq!(existing_ty, &ty);
                } else {
                    concrete_type_variables.insert(tvname.clone(), ty.clone());
                }
            }
        }
    }

    let chosen_method = chosen_method_ty.0.as_method().unwrap().0;
    let unresolved_ret_ty = (*chosen_method.ret).clone();
    let ret_ty = match &unresolved_ret_ty {
        Type::TypeVariable { id: type_var_name, .. } => {
            // FIXME: If this panics, that means that we haven't resolved the return type
            if let Some(concrete_ty) = concrete_type_variables.get(type_var_name) {
                concrete_ty.clone()
            } else {
                Type::TypeVariable {
                    id: type_var_name.clone(),
                    implements: type_variable_impls.get(type_var_name).cloned().map(|x| x.into_iter().collect())
                }
            }
        },
        _ => unresolved_ret_ty
    };

    println!("TYPE VAR ASSIGNMENTS = {concrete_type_variables:?}");
    println!(" - IMPLS");
    for (k, v) in type_variable_impls {
        println!("    - {k} {}", v.iter().map(|x| format!("{x}")).collect::<Vec<_>>().join(", "));
    }
    println!(" - RETURN TYPE = {ret_ty}");

    Ok(MethodResolution {
        method_ty: chosen_method_ty.0,
        data: chosen_method_ty.1,
        ret_ty: ret_ty,
    })
}