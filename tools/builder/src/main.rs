use anyhow::{anyhow, bail, Context as _, Result};
use std::env::consts::EXE_SUFFIX;
use std::fs;
use std::io;
use std::path::Path;
use std::process::Command;
use std::time;

fn timeit(f: impl FnOnce() -> Result<()>) -> Result<time::Duration> {
    let start = time::Instant::now();
    f()?;
    Ok(time::Instant::now().duration_since(start))
}

fn touch(path: &Path) -> io::Result<()> {
    use std::io::Write as _;

    let mut f = fs::OpenOptions::new().append(true).open(path)?;
    f.write_all(&[b'\n'])?;
    Ok(())
}

fn size(path: &Path) -> io::Result<u64> {
    let m = fs::metadata(path)?;
    Ok(m.len())
}

fn cargo(path: &Path, command: &str, args: &[&str]) -> Result<()> {
    println!("cargo {}: {}: {:?}", command, path.display(), args);

    let status = Command::new("cargo")
        .arg(command)
        .current_dir(path)
        .args(args)
        .status()?;

    if !status.success() {
        bail!("failed to run command: {}", status)
    }

    Ok(())
}

#[derive(Debug)]
struct Project {
    name: String,
    d_build: time::Duration,
    build: time::Duration,
    d_rebuild: time::Duration,
    rebuild: time::Duration,
    d_size: u64,
    size: u64,
}

fn main() -> anyhow::Result<()> {
    let mut results = Vec::new();

    let projects = Path::new("projects");

    for f in std::fs::read_dir(projects.join("project"))? {
        let f = f?;
        let path = f.path();

        println!("building: {}", path.display());

        let name = match path.file_stem() {
            Some(name) => name
                .to_str()
                .ok_or_else(|| anyhow!("project name not a string"))?
                .to_owned(),
            None => continue,
        };

        cargo(&projects, "clean", &[])?;

        let bin = format!("{}-project", name);

        let d_build = timeit(|| cargo(&path, "build", &[]))?;
        let build = timeit(|| cargo(&path, "build", &["--release"]))?;

        let main_rs = path.join("src").join("main.rs");
        touch(&main_rs).with_context(|| anyhow!("failed to touch: {}", main_rs.display()))?;

        let d_rebuild = timeit(|| cargo(&path, "build", &[]))?;
        let rebuild = timeit(|| cargo(&path, "build", &["--release"]))?;

        let bin = format!("{}{}", bin, EXE_SUFFIX);
        let debug_bin = projects.join("target").join("debug").join(&bin);
        let release_bin = projects.join("target").join("release").join(&bin);

        let d_size = size(&debug_bin)?;
        let size = size(&release_bin)?;

        results.push(Project {
            name,
            d_build,
            build,
            d_rebuild,
            rebuild,
            d_size,
            size,
        });
    }

    cargo(&projects, "fmt", &[])?;

    println!("| project    | cold build (release) | rebuild* (release) | size (release) |");
    println!("|------------|----------------------|--------------------|----------------|");

    for project in results {
        let extra = if project.name == "clap" { "**" } else { "" };

        println!(
            "| {name}{extra} | {d_build:?} ({build:?}) | {d_rebuild:?} ({rebuild:?}) | {d_size}k ({size}k) |",
            name = project.name,
            extra = extra,
            d_build = project.d_build,
            build = project.build,
            d_rebuild = project.d_rebuild,
            rebuild = project.rebuild,
            d_size = project.d_size / 1024,
            size = project.size / 1024,
        );
    }

    Ok(())
}
