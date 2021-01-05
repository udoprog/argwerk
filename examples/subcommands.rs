argwerk::define! {
    /// Remove something.
    #[usage = "remove"]
    struct Remove {
        help: bool,
    }
    ["-h" | "--help"] => {
        println!("{}", HELP);
        help = true;
    }
}

argwerk::define! {
    /// Add something.
    #[usage = "add"]
    struct Add {
        args: Vec<String>,
        help: bool,
    }
    ["-h" | "--help"] => {
        println!("{}", HELP);
        help = true;
    }
    [arg] => {
        args.push(arg);
    }
}

#[derive(Debug)]
enum Command {
    Remove(Remove),
    Add(Add),
}

argwerk::define! {
    /// A command touring the capabilities of argwerk.
    #[usage = "tour [-h]"]
    struct Args {
        help: bool,
        #[required = "must use a subcommand"]
        command: Command,
    }
    ["-h" | "--help"] => {
        println!("{}", HELP);
        help = true;
    }
    /// Subcommand to remove something.
    ["rm", #[rest(os)] args] if command.is_none() => {
        command = Some(Command::Remove(Remove::parse(args)?));
    }
    /// Subcommand to add something.
    ["add", #[rest(os)] args] if command.is_none() => {
        command = Some(Command::Add(Add::parse(args)?));
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::args()?;

    if args.help {
        return Ok(());
    }

    match args.command {
        Command::Add(add) => {
            if add.help {
                return Ok(());
            }

            println!("Adding: {:?}", add);
        }
        Command::Remove(rm) => {
            if rm.help {
                return Ok(());
            }

            println!("Removing: {:?}", rm);
        }
    }

    Ok(())
}
