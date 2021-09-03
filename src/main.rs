use solidity_egg::*;
use clap::Clap;

#[derive(Clap)]
#[clap(rename_all = "kebab-case")]
pub enum Command {
    // only one command for now
    Optimize(OptParams)
}

// Entry point
pub fn main() {
    let _ = env_logger::builder().try_init();
    match Command::parse() {
        Command::Optimize(params) => {
            let opt = TacOptimizer::new(params);
            opt.run()
        }
    }
}