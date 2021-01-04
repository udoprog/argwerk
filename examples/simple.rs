fn main() -> Result<(), argwerk::Error> {
    let args = argwerk::args! {
        /// A simple tool.
        "tool [-h]" {
            help: bool,
            limit: usize = 10,
        }
        /// The limit of the operation. (default: 10).
        ["-l" | "--limit", int] => {
            limit = str::parse(&int)?;
        }
        /// Print this help.
        ["-h" | "--help"] => {
            println!("{}", HELP);
            help = true;
        }
    }?;

    if args.help {
        return Ok(());
    }

    dbg!(args);
    Ok(())
}
