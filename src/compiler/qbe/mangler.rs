use crate::compiler::ValueType;

/// Mangle a function's name given its arg types, return type and name.
/// For example, a function with the signature `fn printc(i8 c) → null` is mangled to `v_c_printc`.
/// 
/// See [the docs](https://mosaic.ljpprojects.org/docs/mangling) for more info.
fn mangle_function<'a, T: ValueType<'a>>(arg_types: Vec<T>, ret_type: T, name: String) -> String {
    format!("{ret_type}_{A}_{name}", A = arg_types.iter().map(|a| a.to_string()).collect::<Vec<_>>().join("_"))
}

fn function_from_mangled<'a, T: ValueType<'a>>(mangled: String) -> Option<(Vec<T>, T, String)> {
    let mut iter = mangled.chars();

    let ret_type = T::from_iter(&mut iter).ok()?;
    let mut arg_types: Vec<T> = vec![];
    
    iter.next()?;

    loop {
        let Ok(ty) = T::from_iter(&mut iter) else {
            break
        };

        arg_types.push(ty);
    }
    
    let name = iter.collect::<String>();

    Some((arg_types, ret_type, name))
}