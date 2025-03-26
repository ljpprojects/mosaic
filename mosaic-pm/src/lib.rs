mod config;

use semver::VersionReq;
use serde::Deserialize;
use worker::*;

#[derive(Deserialize)]
struct GetQuery {
    name: String,
    version: VersionReq,
}

#[event(fetch)]
async fn fetch(
    req: Request,
    env: Env,
    _ctx: Context,
) -> Result<Response> {
    console_error_panic_hook::set_once();

    let db = env.d1("MPM_DB")?;

    match &*req.path() {
        "getpkg" => {
            let query: GetQuery = req.query()?;
            //let meta = db.exec("");

            Response::ok("wow")
        }
        _ => Response::error("No such method for MosaicPM API", 404)
    }
}