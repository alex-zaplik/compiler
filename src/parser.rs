use std::collections::HashMap;

use pest::iterators::Pair;
use pest::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct CodeParser;

pub struct ParseErrorStep {
    pub row: usize,
    pub col: usize,
    pub reason: String,
}

pub struct ParseError {
    pub info: Vec<ParseErrorStep>,
    pub msg: String,
}

pub enum Error {
    Pest(pest::error::Error<Rule>),
    Parse(ParseError),
}

impl From<pest::error::Error<Rule>> for Error {
    fn from(value: pest::error::Error<Rule>) -> Self {
        Error::Pest(value)
    }
}

impl From<ParseError> for Error {
    fn from(value: ParseError) -> Self {
        Error::Parse(value)
    }
}

#[derive(Debug)]
pub struct Identifier {
    row: usize,
    col: usize,
}

#[derive(Debug)]
pub enum Value {
    Ident(Identifier),
    Val(u64),
}

#[derive(Debug)]
pub enum Operator {
    Add, Sum, Mul, Div, Mod
}

#[derive(Debug)]
pub enum Comparator {
    Eq, Ne, Gt, Lt, Ge, Le
}

#[derive(Debug)]
pub struct Expression {
    lhs: Value,
    rhs: Option<Value>,
    op: Option<Operator>,
}

#[derive(Debug)]
pub struct Condition {
    lhs: Value,
    rhs: Value,
    op: Comparator,
}

pub enum Command {
    Set { val: Value, expr: Expression },
    Read { val: Value },
    Write { val: u64 },
    If { cond: Condition, then: Vec<Command> },
    IfElse { cond: Condition, if_true: Vec<Command>, if_false: Vec<Command> },
    While { cond: Condition, block: Vec<Command> },
    Repeat { cond: Condition, block: Vec<Command> },
    // TODO: Call { procedure },
}

pub struct Function<'a> {
    args: HashMap<&'a str, Identifier>,
    vars: HashMap<&'a str, Identifier>,
    cmds: Vec<Command>,
}

impl<'a> Function<'a> {
    fn new() -> Self {
        Self {
            args: HashMap::new(),
            vars: HashMap::new(),
            cmds: Vec::new(),
        }
    }

    fn parse_declarations(&mut self, declarations: Pair<'a, Rule>) -> Result<(), ParseError> {    
        for decl in declarations.into_inner() {
            // Decl is always an identifier here
            let (row, col) = decl.line_col();
    
            if self.vars.contains_key(decl.as_str()) {
                let prev = self.vars.get(decl.as_str()).unwrap();
                return Err(ParseError {
                    info: vec![ParseErrorStep {
                        row: row,
                        col: col,
                        reason: format!("Identifier '{}' in line {}", decl.as_str(), row),
                    }, ParseErrorStep {
                        row: prev.row,
                        col: prev.col,
                        reason: format!("Already declared here in line {}", prev.row),
                    }],
                    msg: String::from("Identifier already declared:"),
                })
            }
            
            self.vars.insert(decl.as_str(), Identifier { row, col });
        }
    
        Ok(())
    }
    
    fn parse_commands(&mut self, commands: Pair<Rule>) -> Result<(), ParseError>{
        for cmd in commands.into_inner() {
            match cmd.as_rule() {
                Rule::cmd_set => {
                    // TODO: self.cmds.push(Command::Set { lhs: , rhs: (), op: () });
                }
    
                x => println!("Unexpected rule: {:?}", x),
            }
        }
    
        Ok(())
    }

    fn parse_function(function: Pair<'a, Rule>) -> Result<Self, ParseError> {
        let mut fun = Function::new();
    
        for element in function.into_inner() {
            match element.as_rule() {
                Rule::declarations => fun.parse_declarations(element)?,
                Rule::commands => fun.parse_commands(element)?,
    
                x => println!("104: Unexpected rule: {:?}", x),
            }
        }
    
        Ok(fun)
    }
}

// TODO: This should be the result of a parse
pub struct Program<'a> {
    procedures: HashMap<&'a str, Function<'a>>,
    main: Function<'a>,
}

fn parse_procedure<'a>(procedure: Pair<'a, Rule>) -> Result<Function<'a>, ParseError> {
    print!("Procedure ");

    for elem in procedure.into_inner() {
        match elem.as_rule() {
            Rule::proc_head => {
                println!("{}!", elem.as_str());
            }

            Rule::function => {
                return Function::parse_function(elem);
            }
    
            x => println!("125: Unexpected rule: {:?}", x),
        }
    }

    Ok(Function::new())
}

fn parse_main<'a>(main: Pair<'a, Rule>) -> Result<Function<'a>, ParseError> {
    println!("Main!");
    Function::parse_function(main.into_inner().next().unwrap())
}

pub fn parse(input: &str) -> Result<(), Error> {
    let tree = CodeParser::parse(Rule::program_all, input)?.next().unwrap();

    for element in tree.into_inner() {
        match element.as_rule() {
            Rule::procedure => {
                let res = parse_procedure(element)?;
                println!("{:?}", res.vars);

                // TODO: Do something with a procedure
            }

            Rule::main => {
                let res = parse_main(element)?;
                println!("{:?}", res.vars);

                // TODO: Do something with main
            }
    
            Rule::EOI => (),
            x => println!("Unexpected rule: {:?}", x),
        }
    }

    Ok(())
}
