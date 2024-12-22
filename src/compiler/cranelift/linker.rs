use std::process::{exit, Command, Stdio};
use colored::Colorize;
use crate::compiler::cranelift::module::CraneliftModule;

pub struct Linker;

impl Linker {
    pub fn link(module: CraneliftModule) {
        let home = std::env::var("HOME").unwrap();
        let mut dist = module.mosaic_file;
        
        dist.set_file_name(module.name.clone());
        
        let link_command = if std::env::var("TEST").unwrap() == "1" {
            format!(
                "gcc -O3 -pie -arch arm64 -dead_strip -flto -o {DIST} {MODS} {MAIN}",
                DIST = dist.to_str().unwrap(),
                MODS = module.prev_includes.iter().flat_map(|(m, a)| {
                    let mut m = m.clone();

                    m.set_extension("cmp.o");

                    if let Some(a) = a {
                        [m.into_os_string().into_string().unwrap(), a.clone().into_os_string().into_string().unwrap()]
                    } else {
                        [m.into_os_string().into_string().unwrap(), "".into()]
                    }
                }).collect::<Vec<_>>().join(" "),
                MAIN = module.out_file.to_str().unwrap(),
            )
        } else {
            format!(
                "gcc -O3 -pie -dead_strip -flto -o {DIST} {MODS} {MAIN}",
                DIST = dist.to_str().unwrap(),
                MODS = module.prev_includes.iter().flat_map(|(m, a)| {
                    let mut m = m.clone();

                    m.set_extension("cmp.o");

                    if let Some(a) = a {
                        [m.into_os_string().into_string().unwrap(), a.clone().into_os_string().into_string().unwrap()]
                    } else {
                        [m.into_os_string().into_string().unwrap(), "".into()]
                    }
                }).collect::<Vec<_>>().join(" "),
                MAIN = module.out_file.to_str().unwrap(),
            )
        };
        
        print!("{}", "Linking with command: ".bold().green());
        println!("{}", link_command.yellow());
        
        let out = Command::new("sh")
            .arg("-c")
            .arg(link_command)
            .stderr(Stdio::piped())
            .stdout(Stdio::null())
            .spawn()
            .unwrap()
            .wait_with_output()
            .unwrap();
        
        if !out.status.success() {
            print!("{}", "Error during linking: ".bold().red());
            println!("{}", String::from_utf8(out.stderr).unwrap().red());
            
            exit(out.status.code().unwrap());
        }
        
        print!("{}", "Linked executable successfully: ".bold().green());
        println!("{}", dist.to_str().unwrap().green());
    }
}