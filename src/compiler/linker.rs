use crate::compiler::CodeGen;
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::{AstNode, ParseError, StreamedParser};
use crate::reader::CharReader;
use std::fs;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

#[derive(Debug, Clone, PartialEq)]
pub struct MosaicModule {
    obj_file: Option<PathBuf>,
    mosaic_file: PathBuf,
}

impl MosaicModule {
    pub fn new_native(mosaic_file: PathBuf) -> Self {
        MosaicModule {
            obj_file: None,
            mosaic_file,
        }
    }

    pub fn new_external(obj_file: PathBuf, mosaic_file: PathBuf) -> Self {
        MosaicModule {
            obj_file: Some(obj_file),
            mosaic_file,
        }
    }

    pub fn get_obj_file(&self) -> Option<PathBuf> {
        self.obj_file.clone()
    }

    pub fn get_mosaic_file(&self) -> PathBuf {
        self.mosaic_file.clone()
    }
}

pub struct Linker<'a> {
    main_file: PathBuf,
    modules: Vec<&'a MosaicModule>,
    mod_name: &'a str,
}

impl<'a> Linker<'a> {
    pub fn new(main_file: PathBuf, mod_name: &'a str) -> Self {
        Self {
            main_file,
            modules: vec![],
            mod_name,
        }
    }

    pub fn add_module(&mut self, module: &'a MosaicModule) {
        self.modules.push(module)
    }

    pub fn link(&self) -> Result<(), Box<[ParseError]>> {
        let reader = CharReader::new(
            File::new(self.main_file.as_os_str().to_str().unwrap().to_string()).unwrap(),
        );

        let lexer = StreamedLexer::new(reader);
        let mut parser = StreamedParser::new(lexer);

        let mut nodes: Vec<AstNode> = vec![];
        let mut errors: Vec<ParseError> = vec![];

        while let Some(node) = parser.next_ast_node() {
            match node {
                Ok(node) => nodes.push(node),
                Err(error) => errors.push(error),
            }
        }

        if !errors.is_empty() {
            return Err(errors.into_boxed_slice());
        }

        let mut cg = CodeGen::new(nodes.into_boxed_slice());

        let obj_file = &format!("{}.o", self.mod_name);
        let asm_file = &format!("{}.s", self.mod_name);
        let ir_file = &format!("{}.ssa", self.mod_name);

        let generated = cg.generate().unwrap();

        let mut f = fs::File::create(ir_file).unwrap();

        write!(f, "{}", generated).unwrap();

        let mut lib_qbe_paths: Vec<String> = vec![ir_file.into()];
        let mut lib_obj_paths: Vec<String> = vec![obj_file.into()];

        for module in cg.used_modules {
            if let Some(lib_obj_path) = module.obj_file {
                lib_obj_paths.push(lib_obj_path.into_os_string().into_string().unwrap());
            }

            let mut ir_file = module.mosaic_file.clone();

            ir_file.set_extension("ssa");

            let reader = CharReader::new(
                File::new(module.mosaic_file.to_str().unwrap().to_string()).unwrap(),
            );

            let lexer = StreamedLexer::new(reader);
            let mut parser = StreamedParser::new(lexer);

            let mut nodes: Vec<AstNode> = vec![];

            while let Some(node) = parser.next_ast_node() {
                nodes.push(node.unwrap())
            }

            // Generate QBE IR

            let mut cg = CodeGen::new(nodes.into_boxed_slice());

            let generated = cg.generate().unwrap();

            let mut f = BufWriter::new(fs::File::create(ir_file.clone()).unwrap());
            let ir = generated.to_string();

            write!(f, "{ir}").unwrap();

            lib_qbe_paths.push(ir_file.into_os_string().into_string().unwrap());
        }

        // Convert QBE IR into an assembly file

        let qbe_command = format!("qbe -o {asm_file} {}", lib_qbe_paths.join(" "));

        Command::new("sh")
            .arg("-c")
            .arg(qbe_command)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .stdin(Stdio::null())
            .spawn()
            .unwrap()
            .wait()
            .unwrap();

        // Assemble generated assembly

        let c = Command::new("sh")
            .arg("-c")
            .arg(format!("/usr/bin/arch -arm64 as -o {obj_file} {asm_file}"))
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .stdin(Stdio::null())
            .spawn()
            .unwrap()
            .wait()
            .unwrap();

        assert!(c.success());

        // Link generated object files and module object files

        let link_command = format!(
            "/usr/bin/arch -arm64 gcc -e _main -arch arm64 -flto -o {} {}",
            self.mod_name,
            lib_obj_paths.join(" ")
        );

        let c = Command::new("sh")
            .arg("-c")
            .arg(link_command)
            /*.stdout(Stdio::null())
            .stderr(Stdio::null())
            .stdin(Stdio::null())*/
            .spawn()
            .unwrap()
            .wait()
            .unwrap();

        assert!(c.success());

        for ir_file in lib_qbe_paths {
            //fs::remove_file(ir_file).unwrap();
        }

        fs::remove_file(obj_file).unwrap();
        //fs::remove_file(asm_file).unwrap();

        Ok(())
    }
}
