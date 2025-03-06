use std::{env, path::PathBuf};

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let status = std::process::Command::new("rustc")
        .args([
            "--crate-type=cdylib",
            "stub/lib.rs",
            "-o",
            &format!("{}/libagnocast.so", out_dir.display()),
        ])
        .status()
        .expect("failed to compile stub library");

    assert!(status.success(), "rustc failed to compile stub library");

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=dylib=agnocast");
}
