use std::{collections::HashMap, iter};

use batsat::{intmap::AsIndex, lbool, BasicSolver, Lit, SolverInterface, Var};
use smol_str::SmolStr;

use crate::{ast::{Implementation, MethodTy, SpanNode, Type}, eval::EvalError};

/// Recursively build SAT constraints to select exactly one implementation of `name`
/// that takes as input the provided `call_tys`.
/// Returns a map of method vars to their Types, and a fresh `sat_var`
/// that is true iff some implementation holds.
fn add_match_constraints<T>(
    solver: &mut BasicSolver,
    type_variables: &mut HashMap<SmolStr, HashMap<Type, Var>>,
    type_variable_impls: &mut HashMap<SmolStr, Vec<Implementation>>,
    name: &str,
    call_tys: &[Type],
    call_ret_ty: Option<&Type>,
    inside_method: Option<(usize, Var)>,
    get_methods_by_name: &impl Fn(&str) -> Vec<(Type, T)>
) -> (HashMap<Var, (Type, Option<T>)>, Var) {
    println!("{name} | {call_tys:?} {call_ret_ty:?}");
    // Gather candidate methods
    let methods = get_methods_by_name(name)
        .into_iter()
        // filter by arity
        .filter(|m| m.0.as_method().unwrap().params.len() == call_tys.len())
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
            Type::TypeVariable { implements: Some(implements_node), .. } => {
                let (_, list) = implements_node.as_typed().unwrap();
                let implements = list.as_list().unwrap().borrow();
                let implements = implements.iter().map(|i| i.as_implementation().unwrap());
                Some(implements.cloned().collect::<Vec<_>>())
            },
            _ => None
        }
    }).flat_map(|x| x).collect();
    for imp in impls {
        if imp.func == name {
            let v = solver.new_var_default();
            method_vars.insert(v, (Type::Method(imp.method), None));
        }
    }

    // Link parameters
    for (&mvar, (method, _)) in &method_vars {
        println!("METHOD {method}");
        let MethodTy { params: param_tys, ret: ret_ty } = method.as_method().unwrap();
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

                    let (inside_method_idx, inside_method_var) = inside_method.unwrap_or((i, mvar));
                    let type_var_id: SmolStr = if type_var_name == "_" {
                        format!("anon{i}__{mvar:?}").into()
                    } else {
                        format!("{type_var_name}__{mvar:?}").into()
                    };

                    // Bind the type variable to this concrete type under this method
                    let var_map = type_variables
                        .entry(type_var_id.clone())
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
                        if let Some(implements_node) = implements {
                            let (_, list) = implements_node.as_typed().unwrap();
                            let implements = list.as_list().unwrap().borrow();
                            let implements = implements.iter().map(|i| i.as_implementation().unwrap());

                            let impl_map = type_variable_impls
                                .entry(type_var_id.clone())
                                .or_insert_with(Vec::new);
                            impl_map.extend(implements.cloned());
                        }

                        for imp in type_variable_impls.get(&type_var_id).cloned().unwrap_or_default() {
                            println!("RECURSING {}", imp.func);
                            let nested = add_match_constraints(
                                solver,
                                type_variables,
                                type_variable_impls,
                                &imp.func,
                                &imp.method.params,
                                Some(&*imp.method.ret),
                                Some((i, mvar)),
                                get_methods_by_name
                            ).1;
                            // Require: if this method is chosen then nested must hold
                            solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(nested, true)]);
                        }
                    }
                },
                (concrete, Type::TypeVariable { id: type_var_name, implements })
                if !matches!(concrete, Type::TypeVariable { .. })
                => {
                    solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
                    /*let (inside_method_idx, inside_method_var) = inside_method.unwrap_or((i, mvar));
                    let type_var_id: SmolStr = if type_var_name == "_" {
                        format!("anon{inside_method_idx}__{inside_method_var:?}").into()
                    } else {
                        format!("{type_var_name}__{inside_method_var:?}").into()
                    };

                    // Bind the type variable to this concrete type under this method
                    let var_map = type_variables
                        .entry(type_var_id.clone())
                        .or_insert_with(HashMap::new);
                    let bind_var = var_map
                        .entry(concrete.clone())
                        .or_insert_with(|| solver.new_var_default());
                    // m -> binding_is_ty
                    solver.add_clause_reuse(&mut vec![
                        Lit::new(mvar, false),
                        Lit::new(*bind_var, true),
                    ]);

                    println!("TVYOU {param_ty} | {actual}");
                    // panic!("A type variable cannot be cast down to a concrete variable")
                    let mut imp_vars: Vec<Var> = Vec::new();

                    if let Some(implements_node) = implements {
                        let (_, list) = implements_node.as_typed().unwrap();
                        let implements = list.as_list().unwrap().borrow();
                        let implements = implements.iter().map(|i| i.as_implementation().unwrap());

                        let impl_map = type_variable_impls
                            .entry(type_var_id.clone())
                            .or_insert_with(Vec::new);
                        impl_map.extend(implements.cloned());
                    }

                    for imp in type_variable_impls.get(&type_var_id).cloned().unwrap_or_default() {
                        if name == imp.func {
                            //if imp.params.iter().chain(iter::once(&*imp.ret)).nth(i)
                            // Substitute the type variable for the concrete type
                            let substituted_imp_params: Vec<_> = imp.method.params.iter().map(|p| match p {
                                Type::TypeVariable { id, .. } if id == type_var_name => concrete,
                                _ => p
                            }).cloned().collect();
                            let substituted_ret_ty = match &*imp.method.ret {
                                Type::TypeVariable { id, .. } if id == type_var_name => concrete,
                                _ => &*imp.method.ret
                            };
                            println!("SUBS: {substituted_imp_params:?} {substituted_ret_ty}");
                            // Issue is that if this fails to find a match, the whole SAT fails (because of the or later) !!!
                            // fixed?
                            let nested = add_match_constraints(
                                solver,
                                type_variables,
                                type_variable_impls,
                                name,
                                substituted_imp_params.as_slice(),
                                Some(substituted_ret_ty),
                                // &imp.params,
                                // Some(&*imp.ret),
                                inside_method,
                                get_methods_by_name
                            ).1;
                            imp_vars.push(nested);
                        }
                    }

                    // m -> one of these
                    println!("IV: {imp_vars:?}");
                    let mut or_clause = imp_vars.into_iter()
                        .map(|v| Lit::new(v, true)).collect::<Vec<_>>();
                    or_clause.push(Lit::new(mvar, false));
                    solver.add_clause_reuse(&mut or_clause);

                    //solver.add_clause_reuse(&mut vec![Lit::new(mvar, true)]);*/
                }
                (
                    Type::TypeVariable { id: type_var_lhs, implements: implements_lhs },
                    Type::TypeVariable { id: type_var_rhs, implements: implements_rhs }
                ) => {
                    // let type_var_id_lhs: SmolStr = format!("{type_var_lhs}__{mvar:?}").into();
                    // let type_var_id_rhs: SmolStr = format!("{type_var_rhs}__{:?}", inside_method.unwrap()).into();
                    let (inside_method_idx, inside_method_var) = inside_method.unwrap_or((i, mvar));
                    let type_var_id_lhs: SmolStr = if type_var_lhs == "_" {
                        format!("anon{i}__{mvar:?}").into()
                    } else {
                        format!("{type_var_lhs}__{mvar:?}").into()
                    };
                    let type_var_id_rhs: SmolStr = if type_var_rhs == "_" {
                        format!("anon{inside_method_idx}__{inside_method_var:?}").into()
                    } else {
                        format!("{type_var_rhs}__{inside_method_var:?}").into()
                    };

                    // Bind the type variable to this concrete type under this method
                    let var_map = type_variables
                        .entry(type_var_id_lhs.clone())
                        .or_insert_with(HashMap::new);
                    let bind_var = var_map
                        .entry(Type::TypeVariable { id: type_var_id_rhs.clone(), implements: None })
                        .or_insert_with(|| solver.new_var_default());
                    // m -> binding_is_ty
                    solver.add_clause_reuse(&mut vec![
                        Lit::new(mvar, false),
                        Lit::new(*bind_var, true),
                    ]);
                    
                    // m -> unify lhs and rhs
                    unify_pairs.push((type_var_id_lhs, type_var_id_rhs));

                    if !param_ty.compatible(actual) {
                        // Exclude this method
                        solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
                        println!("EXCLUDED!!! {param_ty} vs. {actual}");
                    }
                }
                (lhs, rhs) => {
                    // Exclude mismatched concrete types
                    // FIXME: Probably should use .compatible rather than != here?
                    if !lhs.compatible(rhs) {
                        // Exclude this method
                        solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
                        println!("EXCLUDED!!! {lhs} vs. {rhs}");
                    }
                }
            }
        }

        // Unify all pairs under m
        println!("UNIFYING {unify_pairs:?}");
        for (lhs_id, rhs_id) in &unify_pairs {
            let mut lhs_map = type_variables.remove(lhs_id).unwrap_or(HashMap::new());
            let mut rhs_map = type_variables.remove(rhs_id).unwrap_or(HashMap::new());

            let mut all_tys: std::collections::HashSet<Type> = lhs_map.keys().cloned().collect();
            all_tys.extend(rhs_map.keys().cloned());

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
    let vars: Vec<Var> = method_vars.keys().copied().collect();
    for i in 0..vars.len() {
        for j in (i+1)..vars.len() {
            solver.add_clause_reuse(&mut vec![Lit::new(vars[i], false), Lit::new(vars[j], false)]);
        }
    }

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

    // Build constraints for `func` just like an `imp` resolution
    let (method_vars, sat) = add_match_constraints(
        &mut solver,
        &mut type_variables,
        &mut type_variable_impls,
        func_name,
        &call_tys,
        None,
        None,
        &get_methods_by_name
    );

    // XOR(type variable bindings)
    for tv_vars in type_variables.values().map(|v| v.values()) {
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

    let chosen_method = chosen_method_ty.0.as_method().unwrap();
    let unresolved_ret_ty = (*chosen_method.ret).clone();
    let ret_ty = match unresolved_ret_ty {
        Type::TypeVariable { id: type_var_name, .. } => {
            let i = chosen_method.params.len();
            let type_var_id: SmolStr = if type_var_name == "_" {
                format!("anon{i}__{chosen_method_var:?}").into()
            } else {
                format!("{type_var_name}__{chosen_method_var:?}").into()
            };
            // FIXME: If this panics, that means that we haven't resolved the return type
            concrete_type_variables[&type_var_id].clone()
        },
        _ => unresolved_ret_ty
    };

    println!("TYPE VAR ASSIGNMENTS = {concrete_type_variables:?}");
    println!(" - IMPLS = {type_variable_impls:?}");
    println!(" - RETURN TYPE = {ret_ty}");

    Ok(MethodResolution {
        method_ty: chosen_method_ty.0,
        data: chosen_method_ty.1,
        ret_ty: ret_ty,
    })
}