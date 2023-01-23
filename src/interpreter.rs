use std::collections::HashMap;
use std::io::Write;

use crate::ast::*;

#[derive(Debug)]
struct Data<'a> {
    input: &'a Vec<u64>,
    output: Vec<u64>,
    index: usize,
}

impl<'a> Data<'a> {
    fn new(input: &'a Vec<u64>) -> Self {
        Self {
            input,
            output: Vec::new(),
            index: 0
        }
    }

    fn read_input(&mut self) -> Option<u64> {
        let res = if self.index < self.input.len() {
            Some(self.input[self.index])
        } else {
            None
        };

        self.index += 1;
        res
    }

    fn write_output(&mut self, value: u64) {
        self.output.push(value);
    }
}

#[derive(Debug)]
struct Environment {
    vars: HashMap<String, u64>,
}

impl Environment {
    fn get_identifier_by_name(&self, name: &str) -> u64 {
        self.vars[name]
    }

    fn get_identifier(&self, ident: &Identifier) -> u64 {
        self.vars[ident.name()]
    }
    
    fn get_value(&self, val: &Value) -> u64 {
        match val {
            Value::Ident(i) => {
                self.vars[i.name()]
            }
    
            Value::Val(x) => *x,
        }
    }
    
    fn set_value(&mut self, name: &str, val: u64) {
        *self.vars.get_mut(name).unwrap() = val;
    }

    fn new(func: &Function) -> Self {
        Self {
            vars: func.vars.values().map(|v| (v.name().to_owned(), 0)).collect(),
        }
    }
}

fn is_string_numeric(text: &str) -> bool {
    if text.is_empty() {
        return false;
    }

    for c in text.chars() {
        if !c.is_numeric() {
            return false;
        }
    }
    
    true
}

fn read_input(data: Option<&mut Data>) -> u64 {
    match data {
        Some(data) => data.read_input().expect("Run out of input"),
        None => {
            loop {
                let mut input = String::new();
                print!("> ");
                std::io::stdout().flush().unwrap();
                input.clear();
                let _ = std::io::stdin().read_line(&mut input);
                let input = input.trim();

                if !is_string_numeric(&input) {
                    println!("Input error: Please type in a natural number");
                } else {
                    break input.parse().unwrap();
                }
            }
        }
    }
}

fn write_output(value: u64, data: Option<&mut Data>) {
    match data {
        Some(data) => data.write_output(value),
        None => print!("{}", value),
    }
}

fn evaluate_expression(env: &Environment, expr: &Expression) -> u64 {
    let mut val = env.get_value(expr.lhs());

    if let Some(op) = expr.op() {
        let rhs = env.get_value(expr.rhs().unwrap());

        match op {
            Operator::Add => val += rhs,
            Operator::Sub => val -= rhs,
            Operator::Mul => val *= rhs,
            Operator::Div => val /= rhs,
            Operator::Rem => val %= rhs,
        }
    }

    val
}

fn evaluate_condition(env: &Environment, cond: &Condition) -> bool {
    let lhs = env.get_value(cond.lhs());
    let rhs = env.get_value(cond.rhs());

    match cond.op() {
        Comparator::Eq => lhs == rhs,
        Comparator::Ne => lhs != rhs,
        Comparator::Gt => lhs >  rhs,
        Comparator::Lt => lhs <  rhs,
        Comparator::Ge => lhs >= rhs,
        Comparator::Le => lhs <= rhs,
    }
}

fn run_cmd(env: &mut Environment, data: &mut Option<Data>, program: &Program, func: &Function, cmd: &Command) {
    // println!("Running command: {:?}", cmd);

    match cmd {
        Command::Set { ident, expr } => {
            env.set_value(ident.name(), evaluate_expression(&env, expr));
        }

        Command::Read { ident } => {
            let input = read_input(data.as_mut());
            env.set_value(ident.name(), input);
        }

        Command::Write { val } => {
            write_output(env.get_value(val), data.as_mut());
        }

        Command::If { cond, then } => {
            if evaluate_condition(&env, cond) {
                run_cmds(env, data, program, func, then);
            }
        }

        Command::IfElse { cond, if_true, if_false } => {
            if evaluate_condition(&env, cond) {
                run_cmds(env, data, program, func, if_true);
            } else {
                run_cmds(env, data, program, func, if_false);
            }
        }

        Command::While { cond, block } => {
            while evaluate_condition(&env, cond) {
                run_cmds(env, data, program, func, block);
            }
        }

        Command::Repeat { cond, block } => {
            run_cmds(env, data, program, func, block);
            while !evaluate_condition(&env, cond) {
                run_cmds(env, data, program, func, block);
            }
        }

        Command::Call { func } => {
            let called_func = program.procedures.get(func.function_name()).unwrap();
            let mut new_env = Environment::new(called_func);

            for (called, caller) in called_func.args.iter().zip(func.args()) {
                new_env.set_value(called, env.get_identifier(caller))
            }

            run_cmds(&mut new_env, data, program, called_func, &called_func.cmds);

            for (called, caller) in called_func.args.iter().zip(func.args()) {
                env.set_value(caller.name(), new_env.get_identifier_by_name(&called));
            }
        }
    }
}

fn run_cmds(env: &mut Environment, data: &mut Option<Data>, program: &Program, func: &Function, cmds: &Vec<Command>)
{
    for cmd in cmds {
        run_cmd(env, data, program, func, &cmd);
    }
}

pub fn run(input: Option<&Vec<u64>>, program: &Program) -> Option<Vec<u64>> {
    let mut new_env = Environment::new(&program.main);
    let mut data = match input {
        Some(input) => Some(Data::new(input)),
        None => None,
    };

    run_cmds(&mut new_env, &mut data, program, &program.main, &program.main.cmds);

    match data {
        Some(data) => Some(data.output),
        None => None,
    }
}
