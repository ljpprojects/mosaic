# hello World

## Using `extern fn`

**hello.msc**
```
extern fn puts(*u8 s) -> null

fn main(**:0[u8] argv) -> i32 {
    puts("Hello, World!" as *u8)

    return 0
}
```

Compile with:
```shell
mosaic build hello.msc
```

## Using printf

**hello.msc**
```
extern fn printf(*u8 s, *u8... f) -> null

fn main(**:0[u8] argv) -> i32 {
    printf("Hello, %s!" as *u8, "World" as *u8)

    return 0
}
```

Compile with:
```shell
mosaic build hello.msc
```