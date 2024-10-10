fn main() {
    println!("cargo:rustc-link-search=../../install/agnocastlib/lib");
    println!("cargo:rustc-link-lib=agnocast");
}
