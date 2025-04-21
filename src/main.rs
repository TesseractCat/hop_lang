use batsat::{lbool, BasicSolver, Lit, SolverInterface, Var};
use codespan_reporting::{diagnostic::{Diagnostic, Label}, files::SimpleFiles, term::termcolor::{ColorChoice, StandardStream}};
use eval::{Environment, EvalError};
use indexmap::IndexMap;
use logos::{Logos, Span};
use smol_str::SmolStr;
use thiserror::Error;
use std::{cell::RefCell, collections::HashMap, env, fs, hash::{DefaultHasher, Hash, Hasher}, io::BufWriter, mem, rc::Rc};

mod tokenize;
use tokenize::{parse_block, Token};
mod ast;
use ast::{Implementation, Method, Node, NodeValue, Reference, SpanNode, Type};
mod eval;
use eval::{eval, eval_call};

#[derive(Default, Debug, PartialEq)]
pub struct TypeEnvironment {
    static_env: Rc<RefCell<Environment>>,
    bindings: HashMap<SmolStr, Type>,
    functions: HashMap<SmolStr, Vec<Type>>,
    up: Option<Rc<RefCell<Self>>>,
    global: Option<Rc<RefCell<Self>>>
}
impl TypeEnvironment {
    pub fn new() -> Self {
        Self {
            static_env: Rc::new(RefCell::new(Environment::new())),
            ..Default::default()
        }
    }

    pub fn new_child(this: Rc<RefCell<Self>>) -> Self {
        let child_static_env = Environment::new_child(this.borrow().static_env.clone());
        Self {
            static_env: Rc::new(RefCell::new(child_static_env)),
            up: Some(Rc::clone(&this)),
            global: Some(
                if this.borrow().global.is_some() {
                    this.borrow().global.clone().unwrap()
                } else {
                    this
                }
            ),
            ..Default::default()
        }
    }

    pub fn get(&self, name: &SmolStr) -> Option<Type> {
        if let Some(binding) = self.bindings.get(name) {
            Some(binding.clone())
        } else if let Some(up) = self.up.as_ref().map(|r| Rc::clone(&r)) {
            let mut env = up;
            while env.borrow().bindings.get(name).is_none() {
                let up = env.borrow().up.as_ref().map(|r| Rc::clone(&r));
                if let Some(up) = up {
                    env = up;
                } else {
                    break;
                }
            }
            let r = env.borrow().bindings.get(name).cloned();
            r
        } else {
            None
        }
    }
    pub fn get_function(&self, name: &SmolStr) -> Option<Vec<Type>> {
        if let Some(binding) = self.functions.get(name) {
            Some(binding.clone())
        } else if let Some(up) = self.up.as_ref().map(|r| Rc::clone(&r)) {
            let mut env = up;
            while env.borrow().functions.get(name).is_none() {
                let up = env.borrow().up.as_ref().map(|r| Rc::clone(&r));
                if let Some(up) = up {
                    env = up;
                } else {
                    break;
                }
            }
            let r = env.borrow().functions.get(name).cloned();
            r
        } else {
            None
        }
    }
    pub fn has(&self, name: &SmolStr) -> bool {
        self.get(name).is_some()
    }
    pub fn set(&mut self, name: SmolStr, value: Type, shadow: bool) {
        if self.has(&name) && !shadow {
            if let Some(binding) = self.bindings.get_mut(&name) {
                let _ = mem::replace(binding, value);
            } else if let Some(up) = self.up.as_ref().map(|r| Rc::clone(&r)) {
                let mut env = up;
                while env.borrow().bindings.get(&name).is_none() {
                    let up = env.borrow().up.as_ref().map(|r| Rc::clone(&r));
                    if let Some(up) = up {
                        env = up;
                    } else {
                        break;
                    }
                }
                let mut borrow = env.borrow_mut();
                let binding = borrow.bindings.get_mut(&name);
                if let Some(binding) = binding {
                    let _ = mem::replace(binding, value);
                }
            }
        } else {
            self.bindings.insert(name, value.clone());
        }
    }
    pub fn def(&mut self, name: SmolStr, value: Type) {
        if self.functions.contains_key(&name) {
            self.functions.get_mut(&name).unwrap().push(value);
        } else {
            self.functions.insert(name, vec![value]);
        }
    }

    pub fn global_get(&mut self, name: &SmolStr) -> Option<Type> {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().get(name)
        } else {
            self.get(name)
        }
    }
    pub fn global_set(&mut self, name: SmolStr, value: Type) {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().set(name, value, false);
        } else {
            self.set(name, value, false);
        }
    }
    pub fn global_def(&mut self, name: SmolStr, value: Type) {
        if let Some(ref mut global) = self.global {
            global.borrow_mut().def(name, value);
        } else {
            self.def(name, value);
        }
    }
}

/// Recursively build SAT constraints to select exactly one implementation of `name`
/// that takes as input the provided `call_tys`.
/// Returns a map of method vars to their Types, and a fresh `sat_var`
/// that is true iff some implementation holds.
fn add_match_constraints(
    solver: &mut BasicSolver,
    type_variables: &mut HashMap<SmolStr, HashMap<Type, Var>>,
    name: &str,
    call_tys: &[Type],
    inside_method: Option<Var>,
    env: &TypeEnvironment
) -> (HashMap<Var, Type>, Var) {
    println!("{name} | {call_tys:?}");
    // Gather candidate methods
    let methods = env
        .get_function(&name.into())
        .unwrap_or(Vec::new())
        .into_iter()
        // filter by arity
        .filter(|m| m.as_method().unwrap().0.len() == call_tys.len())
        .collect::<Vec<_>>();
    if methods.is_empty() {
        let sat_var = solver.new_var_default();
        solver.add_clause_reuse(&mut vec![Lit::new(sat_var, false)]);
        return (HashMap::new(), sat_var);
    }

    // Create a SAT var per candidate
    let mut method_vars: HashMap<Var, Type> = HashMap::new();
    for method in &methods {
        let v = solver.new_var_default();
        method_vars.insert(v, method.clone());
    }

    // Exactly-one: OR(vars) and pairwise exclusion
    solver.add_clause_reuse(
        &mut method_vars.keys().copied().map(|v| Lit::new(v, true)).collect()
    );
    let vars: Vec<Var> = method_vars.keys().copied().collect();
    for i in 0..vars.len() {
        for j in (i+1)..vars.len() {
            solver.add_clause_reuse(&mut vec![Lit::new(vars[i], false), Lit::new(vars[j], false)]);
        }
    }

    // Link parameters
    for (&mvar, method) in &method_vars {
        let (param_tys, _) = method.as_method().unwrap();
        let mut unify_pairs: Vec<(SmolStr, SmolStr)> = Vec::new();

        for (i, param_ty) in param_tys.iter().enumerate() {
            let actual = &call_tys[i]; // The argument to the function

            match (param_ty, actual) {
                (Type::TypeVariable { id: type_var_name, implements }, concrete) |
                (concrete, Type::TypeVariable { id: type_var_name, implements })
                if !matches!(concrete, Type::TypeVariable { .. })
                => {
                    let type_var_is_param = matches!(param_ty, Type::TypeVariable { .. });
                    println!("TVUS {type_var_name} = {concrete}");

                    // let mut hasher = DefaultHasher::new();
                    // inside_method.unwrap_or(mvar).hash(&mut hasher);
                    // type_var_name.hash(&mut hasher);
                    // let type_var_id = hasher.finish();
                    let v = inside_method.unwrap_or(mvar);
                    let type_var_id = format!("{type_var_name}__{v:?}").into();

                    // Bind the type variable to this concrete type under this method
                    let var_map = type_variables
                        .entry(type_var_id)
                        .or_insert_with(HashMap::new);
                    let bind_var = var_map
                        .entry(concrete.clone())
                        .or_insert_with(|| solver.new_var_default());
                    // m -> binding_is_ty
                    solver.add_clause_reuse(&mut vec![
                        Lit::new(mvar, false),
                        Lit::new(*bind_var, true),
                    ]);
                    // For all constraints on this type variable, recursively handle
                    // m -> type_var_constraints_satisfied
                    if let Some(implements_node) = implements {
                        let (_, list) = implements_node.as_typed().unwrap();
                        let implements = list.as_list().unwrap().borrow();
                        let implements = implements.iter().map(|i| i.as_implementation().unwrap());
                        for imp in implements {
                            println!("RECURSING {}", imp.func);
                            let nested = add_match_constraints(
                                solver,
                                type_variables,
                                &imp.func,
                                &imp.params,
                                if type_var_is_param { Some(mvar) } else { inside_method },
                                env
                            ).1;
                            // Require: if this method is chosen then nested must hold
                            solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(nested, true)]);
                        }
                    }
                },
                (
                    Type::TypeVariable { id: type_var_lhs, implements: implements_lhs },
                    Type::TypeVariable { id: type_var_rhs, implements: implements_rhs }
                ) => {
                    let type_var_id_lhs: SmolStr = format!("{type_var_lhs}__{mvar:?}").into();
                    let type_var_id_rhs: SmolStr = format!("{type_var_rhs}__{:?}", inside_method.unwrap()).into();
                    
                    // m -> unify lhs and rhs
                    unify_pairs.push((type_var_id_lhs, type_var_id_rhs));

                    // Recurse for implementations
                    for (i, implements) in [implements_lhs, implements_rhs].into_iter().enumerate() {
                        let type_var_is_param = i == 0;
                        if let Some(implements_node) = implements {
                            let (_, list) = implements_node.as_typed().unwrap();
                            let implements = list.as_list().unwrap().borrow();
                            let implements = implements.iter().map(|i| i.as_implementation().unwrap());
                            for imp in implements {
                                println!("RECURSING {}", imp.func);
                                let nested = add_match_constraints(
                                    solver,
                                    type_variables,
                                    &imp.func,
                                    &imp.params,
                                    if type_var_is_param { Some(mvar) } else { inside_method },
                                    env
                                ).1;
                                // Require: if this method is chosen then nested must hold
                                solver.add_clause_reuse(&mut vec![Lit::new(mvar, false), Lit::new(nested, true)]);
                            }
                        }
                    }
                }
                (lhs, rhs) => {
                    // Exclude mismatched concrete types
                    // FIXME: Probably should use .compatible rather than != here?
                    if lhs != rhs {
                        // Exclude this method
                        solver.add_clause_reuse(&mut vec![Lit::new(mvar, false)]);
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

pub fn typecheck_call(
    func_symbol: &SpanNode,
    func: &str,
    args: impl Iterator<Item = Type>,
    env: &Rc<RefCell<TypeEnvironment>>
) -> Result<Type, EvalError> {
    let call_tys: Vec<_> = args.collect();
    let env_borrow = env.borrow();
    let mut solver = BasicSolver::default();
    let mut type_variables = HashMap::new();

    // Build constraints for `func` just like an `imp` resolution
    let (method_vars, sat) = add_match_constraints(
        &mut solver,
        &mut type_variables,
        func,
        &call_tys,
        None,
        &*env_borrow
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
        .ok_or(EvalError::NoMethodMatches { span: func_symbol.tag.clone() })?;

    // Extract type variable assignments
    let mut concrete_type_variables = HashMap::new();
    println!("{type_variables:?}");
    for (tvname, tvmap) in type_variables {
        for (ty, tyvar) in tvmap {
            println!("{tyvar:?} = {:?}", solver.value_var(tyvar));
            if solver.value_var(tyvar) == lbool::TRUE {
                if let Some(existing_ty) = concrete_type_variables.get(&tvname) {
                    assert_eq!(existing_ty, &ty);
                } else {
                    concrete_type_variables.insert(tvname.clone(), ty.clone());
                }
            }
        }
    }

    println!("TYPE VAR ASSIGNMENTS = {concrete_type_variables:?}");

    return Ok(chosen_method_ty);

    Err(EvalError::NoMethodMatches { span: func_symbol.tag.clone() })
}

fn typecheck(node: &SpanNode, env: &Rc<RefCell<TypeEnvironment>>) -> Result<Type, EvalError> {
    let get_methods = |func: &str| -> Option<Vec<Type>> {
        Some(env.borrow().functions.get(&SmolStr::from(func))?.clone())
    };
    match &node.node {
        NodeValue::Bool(_) => Ok(Type::Bool),
        NodeValue::Number(_) => Ok(Type::Number),
        NodeValue::String(_) => Ok(Type::String),
        NodeValue::Symbol(name) => {
            Ok(env.borrow_mut().get(&name).ok_or(EvalError::UndefinedVar { name: name.to_string(), span: node.tag.clone() })?.clone())
        },
        NodeValue::Typed(ty, _) => Ok(ty.clone()),
        NodeValue::Type(ty) => Ok(Type::Type(Some(Box::new(ty.clone())))),
        NodeValue::List(list) => {
            let list = list.borrow();
            if list.len() == 0 { return Ok(Type::UntypedList); }
            let mut list = list.iter();
            let first = list.next().unwrap();
            let builtin = first.node.as_symbol().map(|s| s.as_str());
            
            match builtin {
                Some("do") => {
                    let mut last = Type::UntypedList;
                    while let Some(elem) = list.next() {
                        last = typecheck(elem, env)?;
                    }
                    Ok(last)
                },
                Some("let") => {
                    let symbol_node = list.next()
                        .ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let symbol = symbol_node.node.as_symbol()
                        .ok_or(EvalError::TypeMismatch { expected: "Symbol".into(), got: symbol_node.ty(), span: symbol_node.tag.clone() })?;
                    let val = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let val_ty = typecheck(val, env)?;
                    env.borrow_mut().set(symbol.clone(), val_ty, true);
                    Ok(Type::UntypedList)
                },
                Some("set") => {
                    let symbol_node = list.next()
                        .ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let symbol = symbol_node.node.as_symbol()
                        .ok_or(EvalError::TypeMismatch { expected: "Symbol".into(), got: symbol_node.ty(), span: symbol_node.tag.clone() })?;
                    let val = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    if let Some(to_ty) = env.borrow().get(symbol) {
                        let from_ty = typecheck(val, env)?;
                        if from_ty != to_ty {
                            Err(EvalError::TypeMismatch { expected: format!("{}", to_ty), got: from_ty, span: val.tag.clone() })
                        } else {
                            Ok(Type::UntypedList)
                        }
                    } else {
                        Err(EvalError::UndefinedVar { name: symbol.to_string(), span: symbol_node.tag.clone() })
                    }
                },
                Some("struct") => {
                    let table = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    // Ok(Type::Type(Box::new(
                    //     Type::Struct(Box::new(table.clone()))
                    // )))
                    Ok(Type::Type(None))
                },
                Some("fn") => {
                    let params = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let arrow = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let ret = list.next().ok_or(EvalError::ExpectedAdditionalField { span: node.tag.clone() })?;
                    let ret = ret.clone();

                    let param_names: Vec<SmolStr> = params.as_table().unwrap().borrow()
                        .keys().cloned().map(|n| n.into_keyword().unwrap()).collect();
                    let param_tys: Vec<Type> = params.as_table().unwrap().borrow().values().map(|v| v.as_type().unwrap().clone()).collect();
                    let ret_ty = ret.into_type().map_err(|e| EvalError::TypeMismatch { expected: "Type".into(), got: e.ty(), span: e.tag })?;

                    // Recurse typecheck function body
                    let mut new_env = TypeEnvironment::new_child(Rc::clone(env));
                    for (param_name, param_ty) in param_names.iter().zip(param_tys.iter()) {
                        //println!("Setting function env {param} = {arg}");
                        new_env.set(param_name.clone(), param_ty.clone(), true);
                    }
                    let new_env_rc = Rc::new(RefCell::new(new_env));

                    let body = list.next().unwrap();
                    let body_ty = typecheck(body, &new_env_rc)?;
                    if !ret_ty.compatible(&body_ty, &get_methods, &mut Default::default()) {
                        return Err(EvalError::TypeMismatch { expected: format!("{}", ret_ty), got: body_ty, span: body.tag.clone() });
                    }

                    let method_ty = Type::Method { params: param_tys, ret: Box::new(ret_ty) };

                    Ok(method_ty)
                },
                Some("def") => {
                    let func = list.next().unwrap();
                    let method = list.next().unwrap();

                    let method_ty = typecheck(method, env)?;
                    let func_name = func.as_symbol().unwrap();

                    if env.borrow().functions.contains_key(func_name) {
                        env.borrow_mut().functions.get_mut(func_name).unwrap().push(method_ty);
                    } else {
                        env.borrow_mut().functions.insert(func_name.clone(),vec![method_ty]);
                    }

                    Ok(Type::UntypedList)
                },
                Some("print") => {
                    let val = list.next().unwrap();
                    typecheck(val, env)
                },
                Some("call") => {
                    unimplemented!()
                },
                Some(func) => {
                    typecheck_call(first, func, list.map(|e| typecheck(e, env)).collect::<Result<Vec<_>,_>>()?.into_iter(), env)
                },
                _ => {
                    let first_tag = first.tag.clone();
                    let first = typecheck(first, env)?;
                    if let Type::Type(Some(ty)) = first {
                        match &*ty {
                            Type::Struct(fields) => {
                                let fields = fields.as_table().unwrap().borrow();
                                let table = list.next().unwrap().as_table().unwrap();
                                for (k, v) in table.borrow().iter() {
                                    let v_ty = typecheck(v, env)?;

                                    if let Some(expected_ty) = fields.get(k) {
                                        let expected_ty = expected_ty.as_type().unwrap();
                                        if &v_ty != expected_ty {
                                            return Err(EvalError::TypeMismatch { expected: format!("{}", expected_ty), got: v_ty, span: v.tag.clone() });
                                        }
                                    } else {
                                        return Err(EvalError::UnexpectedField { got: k.to_string(), span: v.tag.clone() });
                                    }
                                }
                                Ok(*ty.clone())
                            },
                            Type::Enum(variants) => {
                                let variants = variants.as_table().unwrap().borrow();
                                let enum_tag = list.next().unwrap();
                                assert!(enum_tag.is_keyword());
                                println!("getting {enum_tag:?} from {variants:?}");
                                let variant = variants.get(enum_tag).expect("Invalid variant").as_type().unwrap();
                                let unit_ty = Node::new_type(Default::default(), Type::Unit);
                                let value = list.next().unwrap_or(&unit_ty);

                                let create_variant_list = SpanNode::new_list(Default::default(), Reference::new(
                                    vec![Node::new_type(Default::default(), variant.clone()), value.clone()]
                                ));
                                let got_ty = typecheck(&create_variant_list, env)?;
                                let expected_ty = variant;
                                if got_ty != *expected_ty {
                                    return Err(EvalError::TypeMismatch { expected: format!("{expected_ty}"), got: got_ty, span: first_tag })
                                }
                                Ok(*ty.clone())
                            },
                            Type::String => Ok(Type::String),
                            _ => todo!("{ty}")
                        }
                    } else {
                        todo!("{first}")
                    }
                }
            }
        },
        NodeValue::Table(_) => Ok(Type::UntypedTable),
        _ => todo!("{node}")
    }
}

pub fn eval_static(node: SpanNode, env: &Rc<RefCell<Environment>>) -> Result<SpanNode, EvalError> {
    match node.node {
        NodeValue::Bool(_)
            | NodeValue::Number(_)
            | NodeValue::String(_)
            | NodeValue::Keyword(_)
            | NodeValue::Symbol(_)
            | NodeValue::Type(_)
            | NodeValue::Typed(_, _) => Ok(node),
        NodeValue::List(ref list) => {
            if list.borrow().len() == 0 {
                Ok(node)
            } else {
                let mut list = list.borrow_mut();
                let func_symbol = list.first().cloned().unwrap();
                let mut list_iter = list.iter_mut();
                if let Some(func_symbol) = func_symbol.as_symbol() {
                    let env_ref = env.borrow();
                    if func_symbol.as_str() == "static" {
                        let val = list_iter.nth(1).unwrap();
                        drop(env_ref);
                        return eval(val.clone(), env);
                    } else if let Some(ref node) = env_ref.get(func_symbol) {
                        if node.ty() == Type::Function {
                            let methods = node.as_typed().unwrap().1.as_list().unwrap().borrow();
                            drop(env_ref);
                            for method in methods.iter().map(|m| m.as_method().unwrap().borrow()) {
                                match &*method {
                                    Method::Rust { ty: Type::Macro, callback } => {
                                        //let args = list_iter.skip(1).map(|n| eval_static(n.clone(), env)).collect::<Result<Vec<_>, _>>()?.into_iter();
                                        let args = list_iter.skip(1).map(|n| n.clone()).collect::<Vec<_>>().into_iter();
                                        return eval_static(callback(args, env)?, env);
                                    }
                                    _ => continue
                                }
                            }
                        }
                    }
                }
                for elem in list_iter {
                    let _ = mem::replace(elem, eval_static(elem.clone(), env)?);
                }
                drop(list);
                Ok(node)
            }
        },
        NodeValue::Table(ref table) => {
            {
                let mut t = mem::take(&mut *table.borrow_mut());
                t = t.into_iter().map(|(key, val)| {
                    Ok::<_, EvalError>((
                        eval_static(key, env)?,
                        eval_static(val, env)?
                    ))
                }).collect::<Result<IndexMap<_, _>, _>>()?;
                let _ = mem::replace(&mut *table.borrow_mut(), t);
            }
            Ok(node)
        },
        _ => todo!("{node}")
    }
}

fn main() {
    let filename = env::args().nth(1).expect("Expected file argument");
    let src = fs::read_to_string(&filename).expect("Failed to read file");

    let mut files = SimpleFiles::new();
    let file = files.add(filename, &src);
    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = codespan_reporting::term::Config::default();

    // Tokenize and parse to node tree
    let mut lexer = Token::lexer(src.as_str());
    let tree = match parse_block(&mut lexer) {
        Ok(tree) => tree,
        Err(e) => {
            let diagnostic = Diagnostic::error()
                .with_labels(vec![
                    Label::primary(file, e.span())
                ])
                .with_message(format!("parse: {e}"));

            let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
            return;
        }
    };
    println!("Tree: {tree}");

    // Eval
    let mut global_env = Environment::new();
    global_env.global_set("Unit".into(), Node::new_type(Default::default(), Type::Unit));
    global_env.global_set("Any".into(), Node::new_type(Default::default(), Type::Any));
    global_env.global_set("Type".into(), Node::new_type(Default::default(), Type::Type(None)));
    global_env.global_set("Unknown".into(), Node::new_type(Default::default(), Type::Unknown));
    global_env.global_set("Number".into(), Node::new_type(Default::default(), Type::Number));
    global_env.global_set("Bool".into(), Node::new_type(Default::default(), Type::Bool));
    global_env.global_set("String".into(), Node::new_type(Default::default(), Type::String));
    global_env.global_set("Function".into(), Node::new_type(Default::default(), Type::Number));

    // Special forms
    global_env.def_special_form("list".into(), Box::new(|args, env| {
        let span = args.clone().next().unwrap().tag.clone();
        Ok(Node::new_list(
            span,
            Reference::new(args.map(|arg| eval(arg, env)).collect::<Result<Vec<_>, _>>()?)
        ))
    }));
    global_env.def_special_form("loop".into(), Box::new(|mut args, env| {
        let body = args.next().unwrap();
        loop {
            if let NodeValue::Bool(b) = eval(body.clone(), env)?.node {
                if b { break; }
            }
        }
        Ok(Node::new_list(Default::default(), Reference::new(vec![])))
    }));
    global_env.def_special_form("do".into(), Box::new(|mut args, env| {
        // Create a new scope
        let new_env = Environment::new_child(Rc::clone(env));
        let new_env_rc = Rc::new(RefCell::new(new_env));
        let mut res = Node::new_list(Default::default(), Reference::new(Vec::new()));

        while let Some(arg) = args.next() {
            res = eval(arg, &new_env_rc)?;
        }
        Ok(res)
    }));
    global_env.def_special_form("quote".into(), Box::new(|mut args, env| {
        Ok(args.next().unwrap())
    }));
    global_env.def_special_form("static".into(), Box::new(|mut args, env| {
        let mut res = Node::new_list(Default::default(), Reference::new(Vec::new()));

        if let Some(arg) = args.next() {
            res = eval(arg, &env)?;
        }
        Ok(res)
    }));
    global_env.def_special_form("get".into(), Box::new(|mut args, env| {
        let (ty, var) = eval(args.next().unwrap(), env)?.with_type();
        let key = args.next().unwrap();

        if let NodeValue::Table(map) = var.node {
            Ok(map.borrow().get(&key).unwrap().clone())
        } else if let NodeValue::List(list) = var.node {
            Ok(list.borrow().get(key.into_number().unwrap() as usize).unwrap().clone())
        } else {
            panic!("Can only get from table/list objects, got: {var}")
        }
    }));
    global_env.def_special_form("let".into(), Box::new(|mut args, env| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.borrow_mut().set(name.clone(), value, true);
        }
        Ok(name)
    }));
    global_env.def_special_form("set".into(), Box::new(|mut args, env| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.borrow_mut().set(name.clone(), value, false);
        }
        Ok(name)
    }));
    global_env.def_special_form("global-set".into(), Box::new(|mut args, env| {
        let name = args.next().unwrap();
        let value = eval(args.next().unwrap(), env)?;
        if let NodeValue::Symbol(ref name) = name.node {
            env.borrow_mut().global_set(name.clone(), value);
        }
        Ok(name)
    }));
    global_env.def_special_form("def".into(), Box::new(|mut args, env| {
        let name_symbol = args.next().unwrap();
        let method = eval(args.next().unwrap(), env)?;
        assert!(method.is_method());

        if let NodeValue::Symbol(ref name) = name_symbol.node {
            env.borrow_mut().global_def(name.clone(), method);
        }
        Ok(name_symbol)
    }));
    global_env.def_special_form("local-def".into(), Box::new(|mut args, env| {
        let name_symbol = args.next().unwrap();

        let mut list = vec![Node::new_symbol(Default::default(), "fn".into())];
        list.extend(args);

        let value = eval(Node::new_list(name_symbol.tag.clone(), Reference::new(list)), env)?;
        assert!(value.is_method());
        if let NodeValue::Symbol(ref name) = name_symbol.node {
            env.borrow_mut().def(name.clone(), value);
        }
        Ok(name_symbol)
    }));
    global_env.def_special_form("call".into(), Box::new(|mut args, env| {
        let func_symbol = args.next().unwrap();
        Ok(eval_call(func_symbol.clone(), eval(func_symbol, env)?, args, env)?)
    }));
    global_env.def_special_form("fn".into(), Box::new(|mut args, env| {
        let params = args.next().unwrap(); // let params = eval(args.next().unwrap(), env)?;
        let arrow = args.next().unwrap();
        arrow.node.as_symbol().filter(|s| **s == "->").ok_or(EvalError::Generic(arrow.tag))?;
        let ret_ty = eval(args.next().unwrap(), env)?;
        let block = args.next().unwrap();

        if !params.is_table() {
            return Err(EvalError::TypeMismatch { expected: "Table".to_string(), got: params.ty(), span: params.tag });
        }

        let params = params.into_table()
            .map_err(|n| EvalError::TypeMismatch { expected: "Table".to_string(), got: n.ty(), span: n.tag })?;
        let params = params.borrow();

        let parse_param_type = |node: &SpanNode| -> Result<Type, EvalError> {
            Ok(eval(node.clone(), env)?.into_type().unwrap())
        };

        let func_ty = Type::Method {
            params: params.values().map(|v| parse_param_type(v)).collect::<Result<_, _>>()?,
            ret: Box::new(ret_ty.into_type().map_err(|n| {
                EvalError::TypeMismatch { expected: "Type".to_string(), got: n.ty(), span: n.tag }
            })?)
        };
        Ok(Node::new_method(block.tag.clone(), Reference::new(Method::Hop {
            param_names: params.keys().cloned().map(|n| n.into_keyword().unwrap()).collect(),
            env: Rc::clone(env), body: Box::new(block), ty: func_ty
        })))
    }));
    global_env.def_special_form("if".into(), Box::new(|mut args, env| {
        let cond = eval(args.next().unwrap(), env)?;
        let yes = args.next().unwrap();
        let mut no = None;
        if let Some(else_symbol) = args.next() {
            no = Some(args.next().unwrap());
        }

        if cond.into_bool().unwrap() {
            Ok(eval(yes, env)?)
        } else if let Some(no) = no {
            Ok(eval(no, env)?)
        } else {
            Ok(Node::new_list(Default::default(), Reference::new(vec![])))
        }
    }));
    global_env.def_special_form("imp".into(), Box::new(|mut args, env| {
        let elem: Vec<SpanNode> = args.collect();

        let func_name = elem[0].node.as_symbol().unwrap().clone();
        let param_types: Vec<Type> = elem[1..elem.len()-2].iter().map(|e| {
            Ok::<_, EvalError>(eval(e.clone(), env)?.into_type().unwrap())
        }).collect::<Result<_, _>>()?;
        let ret_type = eval(elem.last().unwrap().clone(), env)?.into_type().unwrap();

        let imp = Implementation {
            func: func_name,
            params: param_types,
            ret: Box::new(ret_type)
        };

        //Ok(Node::new_type(Default::default(), Type::Implements(implementations)))
        Ok(Node::new_implementation(elem[0].tag.clone(), imp))
    }));

    // Methods
    global_env.def_rust_method("+".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_string()
            .map_err(|n| EvalError::TypeMismatch { expected: "String".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_string()
            .map_err(|n| EvalError::TypeMismatch { expected: "String".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_string(Default::default(), (a.to_string() + b.as_str()).into()))
    }), Type::Method { params: vec![Type::String, Type::String], ret: Box::new(Type::String) });
    global_env.def_rust_method("+".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_number(Default::default(), a + b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Number) });
    global_env.def_rust_method("-".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_number(Default::default(), a - b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Number) });
    global_env.def_rust_method("lt".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_bool(Default::default(), a < b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Number) });
    global_env.def_rust_method("=".into(), Box::new(|mut args, env| {
        let a = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        let b = args.next().unwrap().into_number()
            .map_err(|n| EvalError::TypeMismatch { expected: "Number".to_string(), got: n.ty(), span: n.tag })?;
        Ok(Node::new_bool(Default::default(), a == b))
    }), Type::Method { params: vec![Type::Number, Type::Number], ret: Box::new(Type::Bool) });
    global_env.def_rust_method("refeq".into(), Box::new(|mut args, env| {
        let a = eval(args.next().unwrap(), env)?;
        let b = eval(args.next().unwrap(), env)?;
        Ok(Node::new_bool(Default::default(), a == b))
    }), Type::Method { params: vec![Type::Any, Type::Any], ret: Box::new(Type::Bool) });
    let out = Rc::new(RefCell::new(BufWriter::new(std::io::stdout())));
    global_env.def_rust_method("print".into(), Box::new(move |mut args, env| {
        let value = args.next().unwrap();
        //writeln!(out.borrow_mut(), "{value}");
        println!("{value}");
        Ok(value)
    }), Type::Method { params: vec![Type::Any], ret: Box::new(Type::Any) });
    global_env.def_rust_method("struct".into(), Box::new(|mut args, env| {
        let structure = args.next().unwrap();
        assert!(structure.is_table());

        Ok(Node::new_type(Default::default(), Type::Struct(
            Box::new(structure)
        )))
    }), Type::Method { params: vec![Type::UntypedTable], ret: Box::new(Type::Type(None)) });
    global_env.def_rust_method("enum".into(), Box::new(|mut args, env| {
        let enumeration = args.next().unwrap();

        Ok(Node::new_type(Default::default(), Type::Enum(
            Box::new(enumeration)
        )))
    }), Type::Method { params: vec![Type::UntypedTable], ret: Box::new(Type::Type(None)) });
    /*global_env.def_rust_method("List".into(), Box::new(|mut args, env| {
        let ty = args.next().unwrap();

        Ok(Node::new_type(Default::default(), Type::List(
            Box::new(ty.into_type().unwrap())
        )))
    }), Type::Method { params: vec![Type::Type], ret: Box::new(Type::Type) });*/

    // Macros
    global_env.def_rust_macro("def!".into(), Box::new(|mut args, env| {
        let name_symbol = args.next().unwrap();
        let params = args.next().unwrap();
        let arrow = args.next().unwrap();
        let ret_ty = eval(args.next().unwrap(), env)?;
        let block = args.next().unwrap();

        if let NodeValue::Table(ref table) = params.node {
            table.borrow_mut().values_mut().for_each(|val| {
                let mut tmp = Node::new_bool(Default::default(), false);
                mem::swap(val, &mut tmp);
                let mut new_val = Node::new_list(Default::default(), Reference::new(vec![
                    Node::new_symbol(Default::default(), "static".into()),
                    tmp
                ]));
                mem::swap(val, &mut new_val);
            });
        }

        Ok(Node::new_list(Default::default(), Reference::new(vec![
            Node::new_symbol(Default::default(), "def".into()),
            name_symbol, Node::new_list(Default::default(), Reference::new(vec![
                Node::new_symbol(Default::default(), "fn".into()),
                params, arrow, ret_ty, block
            ]))
        ])))
    }));
    global_env.def_rust_macro("new!".into(), Box::new(|mut args, env| {
        let ty = args.next().unwrap();
        let val = args.next().unwrap();

        Ok(Node::new_list(Default::default(), Reference::new(vec![
            Node::new_list(Default::default(), Reference::new(vec![
                Node::new_symbol(Default::default(), "static".into()),
                ty
            ])),
            val
        ])))
    }));

    let global_env_rc = Rc::new(RefCell::new(global_env));
    // Static pass
    let tree = match eval_static(tree, &global_env_rc) {
        Ok(t) => t,
        Err(e) => {
            let diagnostic = Diagnostic::error()
                .with_labels(vec![
                    Label::primary(file, e.span())
                ])
                .with_message(format!("static: {e}"));

            let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
            return;
        }
    };
    println!("Tree: {tree}");

    // Typecheck pass
    let mut type_env = TypeEnvironment::new();
    for (k, v) in global_env_rc.borrow().bindings.iter() {
        //println!("SETTING TE {k} = {v} i.e. {}", v.ty());
        type_env.set(k.clone(), v.ty(), false);
        if v.ty().is_function() {
            for method in v.as_typed().unwrap().1.as_list().unwrap().borrow().iter() {
                //println!(" - {method}");
                type_env.def(k.clone(), method.ty());
            }
        }
    }
    let type_env_rc = Rc::new(RefCell::new(type_env));
    if let Err(e) = typecheck(&tree, &type_env_rc) {
        let diagnostic = Diagnostic::error()
            .with_labels(vec![
                Label::primary(file, e.span())
            ])
            .with_message(format!("typecheck: {e}"));

        let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
        return;
    }

    // Main pass
    let result = eval(tree, &global_env_rc);

    match result {
        Ok(r) => println!("Result: {r}"),
        Err(e) => {
            println!("{:?}", e);
            let diagnostic = Diagnostic::error()
                .with_labels(vec![
                    Label::primary(file, e.span())
                ])
                .with_message(format!("runtime: {e}"));
        
            let writer = StandardStream::stderr(ColorChoice::Always);
            let config = codespan_reporting::term::Config::default();
        
            let _ = codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diagnostic);
        }
    }
}
