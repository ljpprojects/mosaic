#[macro_export]
macro_rules! ptr_op_mut {
    {
        $ptr:expr => $($action:ident $($($arg:expr)+)?),*
    } => {{
        unsafe { $ptr.as_mut().unwrap() }.$(
            $action(
                $($($arg)+),*
            )
        ).*
    }}
}

#[macro_export]
macro_rules! ptr_op_const {
    {
        $ptr:expr => $($action:ident $($($arg:expr)+)?),*
    } => {{
        unsafe { $ptr.as_mut().unwrap() }.$(
            $action(
                $($($arg)+),*
            )
        ).*
    }}
}