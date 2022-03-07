argwerk::define! {
    /// A simple tool.
    #[usage = "tool [-h]"]
    struct Args {
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
}

fn main() -> Result<(), argwerk::Error> {
    let args = Args::args()?;
    if args.help {
        return Ok(());
    }

    dbg!(args);
    Ok(())
}
