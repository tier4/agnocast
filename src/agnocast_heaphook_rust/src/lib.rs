pub fn hello() {
    println!("Hello World");

    // clippy will warn
    for i in 0..10 {
        println!("Hello");
    }
}
