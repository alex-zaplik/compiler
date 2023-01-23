use compiler;

fn main() {
    compiler::parse_sandbox();
    println!();
    compiler::inter_sandbox_a();
    println!();
    compiler::inter_sandbox_b();
    println!();
    compiler::inter_sandbox_c();
}
