# Literals

Literals are constant, statically-known expressions.

## Kinds of Literals

- Path literal
- Identifier literal
- String literal
- Character literal
- Integer literal
- Float literal

## String Literals

String literals have the following grammar:

```
string_static = [^\"]*
escape_params = \( .+ \)
string_escape = \ [a-z]+ escape_params?
string_part = string_template
              | string_escape
              | string_static

string = " string_part* "
```
