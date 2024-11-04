use std::io;
use std::os::unix::fs::FileExt;
use std::path::Path;

#[derive(Debug)]
pub struct File<P>
where
    P: AsRef<Path> + Clone,
{
    path: P,
    file: std::fs::File,
}

impl<P: AsRef<Path> + Clone> File<P> {
    pub fn new(path: P) -> io::Result<Self> {
        Ok(Self {
            path: path.clone(),
            file: std::fs::File::open(path)?,
        })
    }

    pub fn path(&self) -> &Path {
        self.path.as_ref()
    }

    pub fn file(&self) -> std::fs::File {
        self.file.try_clone().unwrap()
    }
}

impl<P: AsRef<Path> + Clone> Clone for File<P> {
    fn clone(&self) -> Self {
        Self {
            path: self.path.clone(),
            file: self.file.try_clone().unwrap(),
        }
    }
}
