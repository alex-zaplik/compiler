use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::*;

use pest::iterators::Pair;
use pest::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct CodeParser;

// Use Pest errors instead for better printing style

#[derive(Debug)]
pub struct ParseErrorStep {
    pub row: usize,
    pub col: usize,
    pub reason: String,
}

#[derive(Debug)]
pub struct ParseError {
    pub info: Vec<ParseErrorStep>,
    pub row: usize,
    pub col: usize,
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

impl<'a> From<Pair<'a, Rule>> for Comparator {
    fn from(value: Pair<Rule>) -> Self {
        match value.as_rule() {
            Rule::eq => Comparator::Eq,
            Rule::ne => Comparator::Ne,
            Rule::gt => Comparator::Gt,
            Rule::lt => Comparator::Lt,
            Rule::ge => Comparator::Ge,
            Rule::le => Comparator::Le,

            _ => unreachable!()
        }
    }
}

impl Function {
    fn get_identifier(&self, token: Pair<Rule>) -> Result<Rc<Identifier>, ParseError> {
        if self.args.contains_key(token.as_str()) {
            Ok(Rc::clone(self.args.get(token.as_str()).unwrap()))
        } else if self.vars.contains_key(token.as_str()) {
            Ok(Rc::clone(self.vars.get(token.as_str()).unwrap()))
        } else {
            let (row, col) = token.line_col();
            Result::Err(ParseError {
                info: vec![ParseErrorStep { row, col, reason: format!("Undeclared variable '{}' in line {}", token.as_str(), row) }],
                msg: String::from("Undeclared variable"),
                row, col,
            })
        }
    }

    fn get_value(&self, token: Pair<Rule>) -> Result<Value, ParseError> {
        let token = token.into_inner().next().unwrap(); 

        match token.as_rule() {
            Rule::identifier => Ok(Value::Ident(self.get_identifier(token)?)),
            Rule::num => Ok(Value::Val(token.as_str().parse().unwrap())),

            _ => unreachable!(),
        }
    }

    fn parse_expression(&self, expr: Pair<Rule>) -> Result<Expression, ParseError> {
        let mut expr = expr.into_inner();
        let lhs = self.get_value(expr.next().unwrap())?;

        if expr.peek().is_none() {
            Ok(Expression::new(lhs, None, None))
        } else {
            Ok(Expression::new(
                lhs,
                Some(Operator::from(expr.next().unwrap())),
                Some(self.get_value(expr.next().unwrap())?),
            ))
        }
    }

    fn parse_condition(&self, cond: Pair<Rule>) -> Result<Condition, ParseError> {
        let mut cond = cond.into_inner();
        Ok(Condition::new(
            self.get_value(cond.next().unwrap())?,
            Comparator::from(cond.next().unwrap()),
            self.get_value(cond.next().unwrap())?,
        ))
    }

    fn parse_function_call(&self, call: Pair<Rule>) -> Result<FuncCall, ParseError> {
        let mut parts = call.into_inner();
        let (row, col) = parts.peek().unwrap().line_col();
        let func = parts.next().unwrap().as_str().to_owned();

        let args: Result<Vec<_>, _> = parts.next().unwrap().into_inner()
            .map(|decl| self.get_identifier(decl)).collect();
    
        Ok(FuncCall::new(func, row, col, args?))
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
                        row: prev.row(),
                        col: prev.col(),
                        reason: format!("Already declared here in line {}", prev.row()),
                    }],
                    msg: String::from("Identifier already declared"),
                    row, col,
                })
            }
            
            let name = decl.as_str().to_owned();
            let ident = Rc::new(Identifier::new(decl.as_str().to_owned(), row, col));

            if use_args {
                self.args.insert(name, ident);
            } else {
                self.vars.insert(name, ident);
            }
        }
    
        Ok(())
    }
    
    fn parse_commands(&mut self, commands: Pair<Rule>) -> Result<Vec<Command>, ParseError> {
        let mut cmds = Vec::new();

        for cmd in commands.into_inner() {
            let cmd = match cmd.as_rule() {
                Rule::cmd_set => {
                    let mut parts = cmd.into_inner();
                    Command::Set {
                        ident: self.get_identifier(parts.next().unwrap())?,
                        expr: self.parse_expression(parts.next().unwrap())?,
                    }
                }

                Rule::cmd_if => {
                    let mut parts = cmd.into_inner();
                    Command::If {
                        cond: self.parse_condition(parts.next().unwrap())?,
                        then: self.parse_commands(parts.next().unwrap())?,
                    }
                }

                Rule::cmd_if_else => {
                    let mut parts = cmd.into_inner();
                    Command::IfElse {
                        cond: self.parse_condition(parts.next().unwrap())?,
                        if_true: self.parse_commands(parts.next().unwrap())?,
                        if_false: self.parse_commands(parts.next().unwrap())?,
                    }
                }

                Rule::cmd_while => {
                    let mut parts = cmd.into_inner();
                    Command::While {
                        cond: self.parse_condition(parts.next().unwrap())?,
                        block: self.parse_commands(parts.next().unwrap())?,
                    }
                }

                Rule::cmd_repeat => {
                    let mut parts = cmd.into_inner();
                    Command::Repeat {
                        block: self.parse_commands(parts.next().unwrap())?,
                        cond: self.parse_condition(parts.next().unwrap())?,
                    }
                }

                Rule::cmd_call => Command::Call { func: self.parse_function_call(cmd.into_inner().next().unwrap())? },
                Rule::cmd_read => Command::Read { ident: self.get_identifier(cmd.into_inner().next().unwrap())? },
                Rule::cmd_write => Command::Write { val: self.get_value(cmd.into_inner().next().unwrap())? },
    
                _ => unreachable!(),
            };

            cmds.push(cmd);
        }
    
        Ok(cmds)
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

        let cmds = fun.parse_commands(parts.next().unwrap())?;
        fun.cmds.extend(cmds);
    
        Ok(fun)
    }
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
                    row: prev.row(), col: prev.col(),
                    reason: format!("Already declared here in line {}", prev.row())
                }],
                msg: String::from("Procedure already declared"),
                row, col,
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

    fn check_func_calls(&self, cmds: &Vec<Command>) -> Result<(), ParseError> {
        for cmd in cmds {
            match cmd {
                Command::Call { func: caller } => {
                    if let Some(called) = self.procedures.get(caller.function_name()) {
                        let expected = called.args_count();
                        let got = caller.args_count();

                        if expected != got {
                            todo!("Incorrect args count: expected={expected} got={got}");
                        }
                    } else {
                        todo!("Unknown procedure '{}'", caller.function_name());
                    }
                }

                Command::If { cond: _, then } => self.check_func_calls(&then)?,
                Command::While { cond: _, block } => self.check_func_calls(&block)?,
                Command::Repeat { cond: _, block } => self.check_func_calls(&block)?,
                Command::IfElse { cond: _, if_true, if_false } => {
                    self.check_func_calls(&if_true)?;
                    self.check_func_calls(&if_false)?;
                }

                _ => (),
            }
        }

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

        program.check_func_calls(&program.main.cmds)?;
        for proc in program.procedures.values() {
            program.check_func_calls(&proc.cmds)?;
        }
    
        Ok(program)
    }
}
