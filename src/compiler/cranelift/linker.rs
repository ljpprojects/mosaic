use crate::cli::Command;
use crate::compiler::cranelift::module::CraneliftModule;
use colored::Colorize;
use std::process::{exit, Stdio};
use std::{fs, process};

pub struct Linker;

impl Linker {
    pub fn link(module: CraneliftModule, command: Command) {
        let _home = std::env::var("HOME").unwrap();
        let mut dist = module.mosaic_file;

        dist.set_file_name(module.name.clone());

        let Command::Build {
            libraries,
            link_command,
            shell_path,
            shell_eval_flag,
            quiet,
            ..
        } = command else {
            unimplemented!()
        };

        let link_command = link_command
            .replace("{INP}", module.out_file.to_str().unwrap())
            .replace("{DST}", dist.to_str().unwrap())
            .replace(
                "{LIB}",
                &[
                    module
                        .prev_includes
                        .iter()
                        .flat_map(|(m, a)| {
                            let mut m = m.clone();

                            m.set_extension("cmp.o");

                            if let Some(a) = a {
                                [
                                    m.into_os_string().into_string().unwrap(),
                                    a.clone().into_os_string().into_string().unwrap(),
                                ]
                            } else {
                                [m.into_os_string().into_string().unwrap(), "".into()]
                            }
                        })
                        .collect::<Vec<_>>(),
                    libraries,
                ]
                .concat()
                .join(" "),
            );
        
        if !quiet {
            print!("{}", "Linking with command: ".bold().green());
            println!("{}", link_command.yellow());
        }

        let out = match process::Command::new(shell_path)
            .arg(shell_eval_flag)
            .arg(link_command)
            .stderr(Stdio::piped())
            .stdout(Stdio::null())
            .spawn()
            .unwrap()
            .wait_with_output()
        {
            Ok(out) => out,
            Err(e) => {
                eprint!("{}", "Failed to link: ".bold().red());
                eprintln!("{}", e.to_string().bold().red());

                fs::remove_file(module.out_file).unwrap();

                exit(1);
            }
        };

        if !out.status.success() {
            print!("{}", "Error during linking: ".bold().red());
            println!("{}", String::from_utf8(out.stderr).unwrap().red());

            fs::remove_file(module.out_file).unwrap();

            exit(out.status.code().unwrap());
        }
        
        if !quiet {
            print!("{}", "Linked successfully: ".bold().green());
            println!("{}", dist.to_str().unwrap().green());
        }

        fs::remove_file(module.out_file).unwrap();
    }
}
