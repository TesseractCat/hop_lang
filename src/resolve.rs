use std::{collections::{HashMap, HashSet}, iter, mem};

use batsat::{intmap::AsIndex, lbool, BasicSolver, Lit, SolverInterface, Var};
use smol_str::SmolStr;

use crate::{ast::{Implementation, MethodTy, SpanNode, Type}, eval::EvalError, typecheck};

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

/// Takes a method type, removes all TV implementations recursively,
/// and collects them into a HashSet per TV.
fn flatten_impls_helper(
    method: &mut MethodTy,
    type_variable_impls: &mut HashMap<SmolStr, HashSet<Implementation>>
) {
    for p in method.params.iter_mut().chain(iter::once(&mut *method.ret)) {
        if let Type::TypeVariable { id, implements } = p {
            if let Some(implements) = implements {
                for imp in implements.iter_mut() {
                    flatten_impls_helper(&mut imp.method, type_variable_impls);
                }
            }
            type_variable_impls.entry(id.clone())
                .or_insert_with(Default::default)
                .extend(implements.as_ref().map(|x| x.as_slice()).unwrap_or(&[]).iter().cloned());
            let _ = mem::replace(implements, None);
        }
    }
}
pub fn flatten_impls(
    method: Type,
    type_variable_impls: &mut HashMap<SmolStr, HashSet<Implementation>>
) -> Type {
    let method_id = *method.as_method().unwrap().1;
    let mut method_ty = method.into_method().unwrap().0;
    flatten_impls_helper(&mut method_ty, type_variable_impls);
    Type::Method(
        method_ty,
        method_id
    )
}

struct ConstraintEnv<'a, F> {
    solver: &'a mut BasicSolver,

    type_variables: &'a mut HashMap<SmolStr, HashMap<Type, Var>>,
    type_variable_impls: &'a mut HashMap<SmolStr, HashSet<Implementation>>,
    unified_type_variables: &'a mut HashMap<(SmolStr, SmolStr), Var>,

    checked_impls: &'a mut HashSet<Implementation>,

    get_methods_by_name: &'a F
}

/// Recursively build SAT constraints to select exactly one implementation of `name`
/// that takes as input the provided `call_tys`.
/// Returns a map of method vars to their Types, and a fresh `sat_var`
/// that is true iff some implementation holds.
fn add_match_constraints<F: Fn(&str) -> Vec<(Type, T)>, T>(
    env: &mut ConstraintEnv<F>,
    name: &str,
    call_tys: &[Type],
    call_ret_ty: Option<&Type>,
    inside_imp: bool
) -> (HashMap<Var, (Type, Option<T>)>, Var) {
    fn recurse<F: Fn(&str) -> Vec<(Type, T)>, T>(
        env: &mut ConstraintEnv<F>,
        mvar: Var,
        type_var_name: &str
    ) {
        for imp in env.type_variable_impls.get(type_var_name).cloned().unwrap_or_default() {
            // No need to recheck identical impls
            // (this avoids infinite recursion)
            if !env.checked_impls.contains(&imp) {
                env.checked_impls.insert(imp.clone());
                println!("RECURSING {}", imp.func);
                let nested = add_match_constraints(
                    env,
                    &imp.func,
                    &imp.method.params,
                    Some(&*imp.method.ret),
                    true
                ).1;
                // Require: if this method is chosen then nested must hold
                env.solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(nested, true)]);
            }
        }
    }

    println!("{name} | {call_tys:?} {call_ret_ty:?}");
    // Gather candidate methods
    let methods = (env.get_methods_by_name)(name)
        .into_iter()
        // filter by arity
        .filter(|m| m.0.as_method().unwrap().0.params.len() == call_tys.len())
        //.map(|m| (rename_tv_names(m.0), m.1))
        .collect::<Vec<_>>();
    if methods.is_empty() {
        let sat_var = env.solver.new_var_default();
        env.solver.add_clause_reuse(&mut vec![Lit::new(sat_var, false)]);
        return (HashMap::new(), sat_var);
    }

    // Create a SAT var per candidate
    let mut method_vars: HashMap<Var, (Type, Option<T>)> = HashMap::new();
    for mut method in methods {
        let v = env.solver.new_var_default();

        // FIXME: Flatten methods here?
        method.0 = flatten_impls(method.0, env.type_variable_impls);

        method_vars.insert(v, (method.0, Some(method.1)));
    }

    // Basically, if we're actually calling a function, we can use imps as a source of truth
    // otherwise we shouldn't
    if !inside_imp {
        let impls: Vec<Implementation> = env.type_variable_impls.iter().flat_map(|(_, hs)| hs).cloned().collect();
        for imp in impls {
            if imp.func == name {
                let v = env.solver.new_var_default();
                method_vars.insert(v, (Type::Method(imp.method, 0), None));
            }
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
                    let var_map = env.type_variables
                        .entry(type_var_name.clone())
                        .or_insert_with(HashMap::new);
                    let bind_var = var_map
                        .entry(concrete.clone())
                        .or_insert_with(|| env.solver.new_var_default());
                    // m -> binding_is_ty
                    env.solver.add_clause_reuse(&mut vec![
                        Lit::new(mvar, false),
                        Lit::new(*bind_var, true),
                    ]);

                    println!("SHOULD I RECURSE? {type_var_name} {:?}", env.type_variable_impls.get(type_var_name));
                    recurse(
                        env,
                        mvar,
                        &type_var_name
                    );
                },
                (concrete, Type::TypeVariable { id: type_var_name, implements })
                if !matches!(concrete, Type::TypeVariable { .. })
                => {
                    // Bind the type variable to this concrete type under this method
                    if inside_imp {
                        let var_map = env.type_variables
                            .entry(type_var_name.clone())
                            .or_insert_with(HashMap::new);
                        let bind_var = var_map
                            .entry(concrete.clone())
                            .or_insert_with(|| env.solver.new_var_default());
                        // m -> binding_is_ty
                        env.solver.add_clause_reuse(&mut vec![
                            Lit::new(mvar, false),
                            Lit::new(*bind_var, true),
                        ]);
                    } else {
                        // Don't bind unless in imp context
                        env.solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
                    }
                }
                (
                    Type::TypeVariable { id: type_var_lhs, implements: implements_lhs },
                    Type::TypeVariable { id: type_var_rhs, implements: implements_rhs }
                ) => {
                    // m -> unify lhs and rhs
                    if type_var_lhs != type_var_rhs {
                        // Submit to unify type variable values later
                        let mut pair = [type_var_lhs.clone(), type_var_rhs.clone()];
                        pair.sort();
                        unify_pairs.push(pair.clone().into());

                        // mvar -> these TV are unified
                        let unified_var = *env.unified_type_variables.entry(pair.into())
                            .or_insert_with(|| env.solver.new_var_default());
                        env.solver.add_clause_reuse(&mut vec![
                            Lit::new(mvar, false),
                            Lit::new(unified_var, true),
                        ]);
                    }

                    println!(" === {param_ty} vs. {actual}");
                    if inside_imp {
                        recurse(
                            env,
                            mvar,
                            &type_var_lhs
                        );
                        recurse(
                            env,
                            mvar,
                            &type_var_rhs
                        );
                    } else {
                        let lhs = Type::TypeVariable {
                            id: type_var_lhs.clone(),
                            implements: env.type_variable_impls.get(type_var_lhs).cloned().map(|x| x.into_iter().collect())
                        };
                        let rhs = Type::TypeVariable {
                            id: type_var_rhs.clone(),
                            implements: env.type_variable_impls.get(type_var_rhs).cloned().map(|x| x.into_iter().collect())
                        };
                        if !lhs.compatible(&rhs, false) {
                            // Exclude this method
                            env.solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
                            println!("EXCLUDED!!! {param_ty} vs. {actual}");
                        }
                    }
                }
                (lhs, rhs) => {
                    // Exclude mismatched concrete types
                    if !lhs.compatible(rhs, false) {
                        // Exclude this method
                        env.solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
                        println!("EXCLUDED!!! {lhs} vs. {rhs}");
                    }
                }
            }
        }

        // Unify all pairs under m
        println!("UNIFYING {unify_pairs:?}");
        // For each pair of TV
        for (lhs_id, rhs_id) in &unify_pairs {
            let mut lhs_map = env.type_variables.remove(lhs_id).unwrap_or(HashMap::new());
            let mut rhs_map = env.type_variables.remove(rhs_id).unwrap_or(HashMap::new());

            let mut all_tys: std::collections::HashSet<Type> = lhs_map.keys().cloned().collect();
            all_tys.extend(rhs_map.keys().cloned());

            // For all possible TV type assignments
            for ty in all_tys {
                println!(" - {ty}");
                let var_lhs = lhs_map.entry(ty.clone()).or_insert_with(|| env.solver.new_var_default());
                let var_rhs = rhs_map.entry(ty.clone()).or_insert_with(|| env.solver.new_var_default());
                // Enforce equivalence under mvar: var_lhs <-> var_rhs
                env.solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(*var_lhs, false), Lit::new(*var_rhs, true)]);
                env.solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(*var_rhs, false), Lit::new(*var_lhs, true)]);
            }

            env.type_variables.insert(lhs_id.clone(), lhs_map);
            env.type_variables.insert(rhs_id.clone(), rhs_map);
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
    let sat_var = env.solver.new_var_default();
    // sat_var -> OR(method_vars)
    let mut or_clause = method_vars.keys().copied()
        .map(|v| Lit::new(v, true)).collect::<Vec<_>>();
    or_clause.push(Lit::new(sat_var, false));
    env.solver.add_clause_reuse(&mut or_clause);
    // each method_var -> sat_var
    for &v in method_vars.keys() {
        env.solver.add_clause_reuse(&mut vec![Lit::new(v, false), Lit::new(sat_var, true)]);
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
    let mut unified_type_variables = HashMap::new();
    let mut checked_impls = HashSet::new();

    let method_ty = MethodTy {
        params: call_tys, ret: Box::new(Type::Unit)
    };
    let method_ty = flatten_impls(Type::Method(method_ty, 0), &mut type_variable_impls)
        .into_method().unwrap().0;
    let call_tys = method_ty.params;

    println!("Resolving '{func_name}':");
    println!(" - CT: {call_tys:?}");
    println!(" - TVI (for CTs): {type_variable_impls:?}");

    // Build constraints for `func` just like an `imp` resolution
    let (method_vars, sat) = add_match_constraints(
        &mut ConstraintEnv {
            solver: &mut solver,
            type_variables: &mut type_variables,
            type_variable_impls: &mut type_variable_impls,
            unified_type_variables: &mut unified_type_variables,
            checked_impls: &mut checked_impls,
            get_methods_by_name: &get_methods_by_name
        },
        func_name,
        &call_tys,
        None,
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