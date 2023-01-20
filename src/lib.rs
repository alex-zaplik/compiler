mod parser;
mod ast;

extern crate pest;
#[macro_use]
extern crate pest_derive;

use ast::Program;
use parser::Error;

fn run_sandbox(input: &str) {
    let result = Program::parse(input);

    match result {
        Err(Error::Parse(err)) => {
            println!("{} --> {}:{}:{}:", err.msg, "filename", err.row, err.col);

            for step in err.info {
                println!(
                    "\n{}\n{}^\n{}{}",
                    input.lines().nth(step.row - 1).unwrap(),
                    " ".repeat(step.col),
                    " ".repeat(step.col),
                    step.reason,
                );
            }
        },
        Err(Error::Pest(err)) => todo!("Print parser errors nicely:{}", err),
        Ok(program) => println!("{:#?}", program),
    }
}

pub fn sandbox() {
    run_sandbox("
        PROCEDURE foo(x, y, z) IS baba
        BEGIN
            x := y + z;
        END

        PROCEDURE bar(a) IS
        VAR
            b, c
        BEGIN
            b := a + 10;
            c := a + 15;

            IF b > a THEN
                IF b > c THEN
                    foo(a, b, c);
                    WRITE 2;
                ENDIF

                WRITE 1;
            ELSE
                WRITE 0;
            ENDIF
        END  

        PROGRAM IS VAR
            a, _a, b
        BEGIN
            a := b + 5;
            _a := a + 1;

            foo(a, _a, b);

            READ a;
            WRITE 15;
        END
    ");
}      
