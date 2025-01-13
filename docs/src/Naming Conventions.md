In Mosaic, you should use snake_case for variable names & functions, and PascalCase for *most* type aliases. If a type alias is not intended for use as a data structure, use either PascalCase or snake_case.

```
let magic_constant: i32 = 1747837849
mut will_be_a_pointer: f64 = 0.8

fn do_stuff() -> null {
	return null
}

type *DataStructure = i32
type int = i32 # convenience alias
```