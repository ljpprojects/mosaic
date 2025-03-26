use crate::cli::{Command, EmitKind};
use crate::compiler::cranelift::module::CraneliftModule;
use crate::compiler::cranelift::CraneliftGenerator;
use crate::file;
use crate::lexer::StreamedLexer;
use crate::parser::StreamedParser;
use crate::reader::CharReader;
use cranelift_codegen::isa::lookup;
use std::collections::HashSet;
use std::process::Stdio;
use std::process;
use target_lexicon::Architecture::Aarch64;
use target_lexicon::OperatingSystem::{Darwin, MacOSX};
use target_lexicon::{Aarch64Architecture, Triple};

pub struct Linker;

impl Linker {
    pub fn link(module: CraneliftModule, command: Command, triple: Triple) -> Result<(), String> {
        let mut dist = module.mosaic_file;

        dist.set_file_name(module.name.clone());

        let Command::Build {
            ref file,
            ref libraries,
            link_flags: ref custom_link_flags,
            ref shell_path,
            ref shell_eval_flag,
            ref no_implicit_functions,
            ref quiet,
            ref out_file,
            ref emit,
            ref target,
            ref linker,
        } = command else {
            unimplemented!()
        };

        let mut link_flags = vec![];

        match emit {
            EmitKind::Binary if triple.operating_system.is_like_darwin() => {
                if matches!(triple.operating_system, Darwin(_) | MacOSX(_)) {
                    link_flags.extend(["-lSystem".to_string(), "-no_pie -syslibroot `xcrun -sdk macosx --show-sdk-path`".to_string(), "-macos_version_min `xcrun -sdk macosx --show-sdk-version`".to_string()]);
                } else {
                    return Err(format!("Cannot compile to darwin-like OS/environment {}.", triple.operating_system));
                }
            }
            EmitKind::StaticBinary => {
                if triple.operating_system.is_like_darwin() {
                    return Err("Linking static binaries on Darwin or Darwin-like OSes is not possible.".into())
                }


            }
            EmitKind::StaticLib => {}
            EmitKind::DynamicLib => {}
            _ => {}
        }

        if let Aarch64(Aarch64Architecture::Aarch64) = triple.architecture {
            link_flags.push("-arch arm64".to_string());
        } else {
            link_flags.push(format!("-arch {}", triple.architecture));
        }


        link_flags.push(format!("-o {}", out_file.clone().unwrap_or(dist.display().to_string())));

        let mut link_files: HashSet<String> = HashSet::from_iter(libraries.clone());

        link_files.insert(module.out_file.display().to_string());

        if let Some(assoc_obj) = module.assoc_obj {
            link_files.insert(assoc_obj.display().to_string());
        }

        for (mosaic_file, assoc_obj) in module.prev_includes {
            let p = mosaic_file.display().to_string();

            let mosaic_file = file::File::new(p).unwrap();
            let reader = CharReader::new(mosaic_file.clone());

            let lexer = StreamedLexer::new(reader);
            let parser = StreamedParser::new(lexer);
            
            let updated_command = Command::Build {
                file: mosaic_file.path().display().to_string(),
                out_file: None,
                libraries: libraries.clone(),
                link_flags: Some(link_flags.join(",")),
                shell_path: shell_path.clone(),
                shell_eval_flag: shell_eval_flag.clone(),
                no_implicit_functions: *no_implicit_functions,
                quiet: *quiet,
                emit: *emit,
                target: Some(triple.to_string()),
                linker: linker.clone(),
            };

            let cg = CraneliftGenerator::new(parser, lookup(triple.clone()).unwrap(), Some(updated_command));
            let compiled = cg.compile(true, assoc_obj).map_err(|e| e.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n"))?;

            link_files.insert(compiled.out_file.display().to_string().replace(" ", "\\ "));

            if let Some(assoc_obj) = compiled.assoc_obj {
                link_files.insert(assoc_obj.display().to_string());
            }
        }
        
        let link_command = format!("{linker} {FLG} {INP}", FLG = custom_link_flags.clone().map(|args| args.replace(",", " ").replace("{DST}", &out_file.clone().unwrap_or(dist.display().to_string()))).clone().unwrap_or(link_flags.join(" ")), INP = link_files.into_iter().collect::<Vec<_>>().join(" "));

        println!("{link_command}");

        let result = process::Command::new(shell_path)
            .arg(shell_eval_flag)
            .arg(link_command)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .stdin(Stdio::null())
            .spawn()
            .map_err(|e| e.to_string())?
            .wait_with_output();

        match result {
            Err(e) => return Err(e.to_string()),
            Ok(r) => {
                if !r.status.success() {
                    return Err(String::from_utf8_lossy(&r.stderr).parse().unwrap())
                }
            }
        }
        
        Ok(())
    }
}
