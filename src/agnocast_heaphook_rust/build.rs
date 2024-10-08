fn main() {
    println!("cargo:rustc-link-search=../../build/agnocastlib");
    println!("cargo:rustc-link-lib=agnocast");
}
