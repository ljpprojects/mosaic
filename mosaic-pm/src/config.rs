use serde::Deserialize;

#[derive(Deserialize, Debug)]
pub struct PackageConfig {
    authors: Vec<String>,
    version: String,
}