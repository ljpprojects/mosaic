#[derive(Debug, Clone, PartialEq)]
pub enum EmitFileFormat {
    /// The default format, a statically linked binary for the given architecture — 'bin'
    Executable,

    /// An assembly file including every module's assembly combined — 'asm'
    StaticAssembly,

    /// Just the entry point's binary — 'obj'
    Object,

    /// A statically linked object file — 'lib'
    StaticObject,

    /// A dynamically linked object file — 'dylib'
    DynamicObject,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Flag {
    Emit(EmitFileFormat),
    DebugInfo(bool),
}
