mod interpreter;
mod parser;
mod error;
mod ast;

extern crate pest;
#[macro_use]
extern crate pest_derive;

use ast::Program;

fn run_sandbox(code: &str, input: Option<&Vec<u64>>) -> Option<Vec<u64>> {
    let program = Program::parse(code);

    match program {
        Err(errs) => {
            for err in errs {
                println!("{}", err.format_with("src/test.path", code));
            }
            None
        }

        Ok(program) => {
            interpreter::run(input, &program)
        }
    }
}

pub fn parse_sandbox() {
    let input = vec![7];
    let result = run_sandbox("
        PROCEDURE foo(x, y, z) IS
        BEGIN
            x := y + z;
            bar(y);
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

            READ _a;
            foo(a, _a, b);

            WRITE 15;
        END
    ", Some(&input));

    match result {
        Some(output) => {
            println!("Input: {:?}", input);
            println!("Output: {:?}", output);
        }
        None => (),
    }
}      

pub fn inter_sandbox_a() {
    run_sandbox("
        PROGRAM IS
        VAR n, p
        BEGIN
            READ n;
            REPEAT
                p := n / 2;
                p := 2 * p;
                IF n > p THEN
                    WRITE 1;
                ELSE
                    WRITE 0;
                ENDIF
                n := n / 2;
            UNTIL n = 0;
        END
    ", None);
    println!();
}

pub fn inter_sandbox_b() {
    let input = vec![210, 3003, 609, 9177];
    let result = run_sandbox("
        PROCEDURE swap(a, b) IS
        VAR c
        BEGIN
            c := a;
            a := b;
            b := c;
        END

        PROCEDURE gcd(a, b, c) IS
        VAR x, y
        BEGIN
            x := a;
            y := b;
            WHILE y != 0 DO
                IF x >= y THEN
                    x := x - y;
                ELSE
                    swap(x, y);
                ENDIF
            ENDWHILE
            c := x;
        END

        PROGRAM IS
        VAR a, b, c, d, x, y, z
        BEGIN
            READ a;
            READ b;
            READ c;
            READ d;
            gcd(a, b, x);
            gcd(c, d, y);
            gcd(x, y, z);
            WRITE z;
        END
    ", Some(&input));

    match result {
        Some(output) => {
            println!("Input: {:?}", input);
            println!("Output: {:?}", output);
        }
        None => (),
    }
}

pub fn inter_sandbox_c() {
    let input = vec![1, 2, 3, 4];
    let result = run_sandbox("
        PROCEDURE write(a, b, c, d) IS
        VAR x
        BEGIN
            x := 0;
            IF a != 0 THEN
                WRITE a;
                write(b, c, d, x);
            ENDIF
        END

        PROGRAM IS
        VAR a, b, c, d
        BEGIN
            READ a;
            READ b;
            READ c;
            READ d;
            write(a, b, c, d);
        END
    ", Some(&input));

    match result {
        Some(output) => {
            println!("Input: {:?}", input);
            println!("Output: {:?}", output);
        }
        None => (),
    }
}
