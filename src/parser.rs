use std::collections::HashMap;
use std::rc::Rc;

use pest::iterators::Pair;
use pest::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct CodeParser;

#[derive(Debug)]
pub struct ParseErrorStep {
    pub row: usize,
    pub col: usize,
    pub reason: String,
}

#[derive(Debug)]
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
    name: String,
    row: usize,
    col: usize,
}

#[derive(Debug)]
pub enum Value {
    Ident(Rc<Identifier>),
    Val(u64),
}

#[derive(Debug)]
pub enum Operator {
    Add, Sub, Mul, Div, Rem
}

impl<'a> From<Pair<'a, Rule>> for Operator {
    fn from(value: Pair<Rule>) -> Self {
        match value.as_rule() {
            Rule::add => Operator::Add,
            Rule::sub => Operator::Sub,
            Rule::mul => Operator::Mul,
            Rule::div => Operator::Div,
            Rule::rem => Operator::Rem,

            _ => unreachable!()
        }
    }
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

#[derive(Debug)]
pub enum Command {
    Set { ident: Rc<Identifier>, expr: Expression },
    Read { val: Value },
    Write { val: u64 },
    If { cond: Condition, then: Vec<Command> },
    IfElse { cond: Condition, if_true: Vec<Command>, if_false: Vec<Command> },
    While { cond: Condition, block: Vec<Command> },
    Repeat { cond: Condition, block: Vec<Command> },
    // TODO: Call { procedure },
}

#[derive(Debug)]
pub struct Function {
    name: String,
    col: usize,
    row: usize,
    args: HashMap<String, Rc<Identifier>>,
    vars: HashMap<String, Rc<Identifier>>,
    cmds: Vec<Command>,
}

impl Function {
    fn new(name: String, col: usize, row: usize) -> Self {
        Self {
            name, col, row,
            args: HashMap::new(),
            vars: HashMap::new(),
            cmds: Vec::new(),
        }
    }

    fn get_identifier(&self, token: Pair<Rule>) -> Result<Option<Rc<Identifier>>, ParseError> {
        if self.args.contains_key(token.as_str()) {
            Ok(Some(Rc::clone(self.args.get(token.as_str()).unwrap())))
        } else if self.vars.contains_key(token.as_str()) {
            Ok(Some(Rc::clone(self.vars.get(token.as_str()).unwrap())))
        } else {
            let (row, col) = token.line_col();
            Result::Err(ParseError {
                info: vec![ParseErrorStep { row, col, reason: format!("Undeclared variable '{}' in line {}", token.as_str(), row) }],
                msg: String::from("Undeclared variable")
            })
        }
    }

    fn get_value(&self, token: Pair<Rule>) -> Result<Option<Value>, ParseError> {
        let token = token.into_inner().next().unwrap(); 

        match token.as_rule() {
            Rule::identifier => Ok(Some(Value::Ident(self.get_identifier(token)?.unwrap()))),
            Rule::num => Ok(Some(Value::Val(token.as_str().parse().unwrap()))),

            _ => unreachable!(),
        }
    }

    fn parse_declarations(&mut self, declarations: Pair<Rule>, use_args: bool) -> Result<(), ParseError> {
        for decl in declarations.into_inner() {
            let (row, col) = decl.line_col();

            let prev = if self.args.contains_key(decl.as_str()) {
                self.args.get(decl.as_str())
            } else if self.vars.contains_key(decl.as_str()) {
                self.vars.get(decl.as_str())
            } else {
                None
            };
    
            if let Some(prev) = prev {
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
            
            let name = decl.as_str().to_owned();
            let ident = Rc::new(Identifier { name: decl.as_str().to_owned(), row, col });

            if use_args {
                self.args.insert(name, ident);
            } else {
                self.vars.insert(name, ident);
            }
        }
    
        Ok(())
    }
    
    fn parse_commands(&mut self, commands: Pair<Rule>) -> Result<(), ParseError> {
        for cmd in commands.into_inner() {
            let cmd = match cmd.as_rule() {
                Rule::cmd_set => {
                    let mut parts = cmd.into_inner();
                    let ident = self.get_identifier(parts.next().unwrap())?.unwrap();
                    let mut expr = parts.next().unwrap().into_inner();

                    let lhs = self.get_value(expr.next().unwrap())?.unwrap();
                    if expr.peek().is_none() {
                        Command::Set { ident, expr: Expression { lhs, op: None, rhs: None }}
                    } else {
                        Command::Set { ident, expr: Expression {
                            lhs: lhs,
                            op: Some(Operator::from(expr.next().unwrap())),
                            rhs: self.get_value(expr.next().unwrap())?,
                        }}
                    }                    
                }

                // TODO: Read, Write, If, IfElse, While, Repeat, Call
    
                _ => unreachable!(),
            };
            self.cmds.push(cmd);
        }
    
        Ok(())
    }

    fn parse_function(name: String, row: usize, col: usize, arguments: Option<Pair<Rule>>, function: Pair<Rule>) -> Result<Self, ParseError> {
        let mut fun = Function::new(name, row, col);

        if let Some(args) = arguments {
            fun.parse_declarations(args, true)?;
        }

        let mut parts = function.into_inner();

        if let Rule::declarations = parts.peek().unwrap().as_rule() {
            fun.parse_declarations(parts.next().unwrap(), false)?;
        }

        fun.parse_commands(parts.next().unwrap())?;
    
        Ok(fun)
    }
}

#[derive(Debug)]
pub struct Program {
    procedures: HashMap<String, Function>,
    main: Function,
}

impl Program {
    fn parse_procedure(&mut self, procedure: Pair<Rule>) -> Result<(), ParseError> {
        let (row, col) = procedure.line_col();

        let mut parts = procedure.into_inner();
        let mut head = parts.next().unwrap().into_inner();
        let name = head.next().unwrap().as_str().to_owned();

        if self.procedures.contains_key(&name) {
            let prev = self.procedures.get(&name).unwrap();

            return Err(ParseError {
                info: vec![ParseErrorStep {
                    row, col,
                    reason: format!("Procedure '{}' in line {}", name, row)
                }, ParseErrorStep {
                    row: prev.row, col: prev.col,
                    reason: format!("Already declared here in line {}", prev.row)
                }],
                msg: String::from("Procedure already declared:"),
            })
        }
        
        self.procedures.insert(name.clone(),
            Function::parse_function(
                name, row, col,
                head.next(),
                parts.next().unwrap(),
        )?);

        Ok(())
    }
    
    fn parse_main(&mut self, main: Pair<Rule>) -> Result<(), ParseError> {
        let (row, col) = main.line_col();

        self.main = Function::parse_function(
            "Main".to_owned(), row, col,
            None,
            main.into_inner().next().unwrap(),
        )?;

        Ok(())
    }
    
    pub fn parse(input: &str) -> Result<Self, Error> {
        let mut program = Program {
            procedures: HashMap::new(),
            main: Function::new("Main".to_owned(), 0, 0),
        };

        let tree = CodeParser::parse(Rule::program_all, input)?.next().unwrap();
    
        for element in tree.into_inner() {
            match element.as_rule() {
                Rule::procedure => program.parse_procedure(element)?,
                Rule::main => program.parse_main(element)?,
        
                Rule::EOI => (),
                _ => unreachable!(),
            }
        }
    
        Ok(program)
    }
}
