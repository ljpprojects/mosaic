use crate::compiler::qbe::QbeGenerator;
use crate::compiler::{GeneratedModule, Generator};
use crate::file::File;
use crate::lexer::StreamedLexer;
use crate::parser::{ParseError, StreamedParser};
use crate::reader::CharReader;
use std::fs;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::process::Command;
use crate::compiler::qbe::errors::QbeGenerationError;
use crate::compiler::qbe::modules::QbeModule;

pub struct QbeLinker<'a> {
    main_file: PathBuf,
    modules: Vec<&'a QbeModule<'a>>,
    mod_name: &'a str,
}

impl<'a> QbeLinker<'a> {
    pub fn new(main_file: PathBuf, mod_name: &'a str) -> Self {
        Self {
            main_file,
            modules: vec![],
            mod_name,
        }
    }

    pub fn add_module(&mut self, module: &'a QbeModule<'a>) {
        self.modules.push(module)
    }

    pub fn link(&self, main_cg: &'a mut QbeGenerator<'a>) -> Result<(), QbeGenerationError> {
        let obj_file = &format!("{}.o", self.mod_name);
        let asm_file = &format!("{}.s", self.mod_name);
        let ir_file = &format!("{}.ssa", self.mod_name);

        let generated = main_cg.generate()?;

        let mut f = fs::File::create(ir_file).unwrap();

        write!(f, "{}", generated).unwrap();

        let mut lib_qbe_paths: Vec<String> = vec![ir_file.into()];
        let mut lib_obj_paths: Vec<String> = vec![obj_file.into()];

        for module in generated.included_modules {
            if let Some(lib_obj_path) = module.assoc_obj_file() {
                lib_obj_paths.push(lib_obj_path.into_os_string().into_string().unwrap());
            }

            // Write QBE IR

            let generated = module.get_ir_repr();

            let mut f = BufWriter::new(fs::File::create(ir_file.clone()).unwrap());
            let ir = generated.to_string();

            write!(f, "{ir}").unwrap();

            lib_qbe_paths.push(module.out_ir_path().into_os_string().into_string().unwrap());
        }

        // Convert QBE IR into an assembly file

        let qbe_command = format!("qbe -o {asm_file} {}", lib_qbe_paths.join(" "));

        Command::new("sh")
            .arg("-c")
            .arg(qbe_command)
            /*.stdout(Stdio::null())
            .stderr(Stdio::null())
            .stdin(Stdio::null())*/
            .spawn()
            .unwrap()
            .wait()
            .unwrap();

        // Assemble generated assembly

        let c = Command::new("sh")
            .arg("-c")
            .arg(format!("/usr/bin/arch -arm64 as -o {obj_file} {asm_file}"))
            /*.stdout(Stdio::null())
            .stderr(Stdio::null())
            .stdin(Stdio::null())*/
            .spawn()
            .unwrap()
            .wait()
            .unwrap();

        assert!(c.success());

        // Link generated object files and module object files

        let link_command = format!(
            "/usr/bin/arch -arm64 gcc -e _main -arch arm64 -flto -O3 -o {} {}",
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
