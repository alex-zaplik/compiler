mod parser;

extern crate pest;
#[macro_use]
extern crate pest_derive;

use parser::Program;
use parser::Error;

fn run_sandbox(input: &str) {
    let result = Program::parse(input);

    match result {
        Err(Error::Parse(err)) => {
            println!("{}", err.msg);

            for step in err.info {
                println!(
                    "{}\n{}^\n{}{}",
                    input.lines().nth(step.row - 1).unwrap(),
                    " ".repeat(step.col),
                    " ".repeat(step.col),
                    step.reason,
                );
            }
        },
        Err(Error::Pest(err)) => println!("{:?}", err),
        Ok(program) => println!("{:#?}", program),
    }
}

pub fn sandbox() {
    run_sandbox("
        PROCEDURE foo(x, y, z) IS
        BEGIN
            x := y + z;
        END

        PROCEDURE bar(a) IS
        VAR
            b
        BEGIN
            b := a + 10;
        END  

        PROGRAM IS VAR
            a, _a, b
        BEGIN
            a := b + 5;
            _a := a + 1;
        END
    ");
}      
