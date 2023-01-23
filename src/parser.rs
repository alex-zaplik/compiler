use std::collections::HashMap;
use std::rc::Rc;
use std::vec;

use crate::ast::*;
use crate::error::Error;

use pest::iterators::Pair;
use pest::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct CodeParser;

impl From<pest::error::Error<Rule>> for Error {
    fn from(value: pest::error::Error<Rule>) -> Self {
        let loc = match value.line_col {
            pest::error::LineColLocation::Pos(pos) => Location::from(pos),
            pest::error::LineColLocation::Span(pos, _) => Location::from(pos),
        };

        let msg = value.variant.message().into_owned();

        Self::new(loc.clone(), msg.clone()).add(loc, msg)
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
    fn get_identifier(&self, token: Pair<Rule>) -> Result<Rc<Identifier>, Error> {
        if self.vars.contains_key(token.as_str()) {
            Ok(Rc::clone(self.vars.get(token.as_str()).unwrap()))
        } else {
            let loc = Location::from(token.line_col());
            Err(Error::new(loc.clone(), "Undeclared variable".to_owned())
                      .add(loc.clone(), format!("Undeclared variable '{}' in line {}", token.as_str(), loc.row())))
        }
    }

    fn get_value(&self, token: Pair<Rule>) -> Result<Value, Error> {
        let token = token.into_inner().next().unwrap(); 

        match token.as_rule() {
            Rule::identifier => Ok(Value::Ident(self.get_identifier(token)?)),
            Rule::num => Ok(Value::Val(token.as_str().parse().unwrap())),

            _ => unreachable!(),
        }
    }

    fn parse_expression(&self, expr: Pair<Rule>) -> Result<Expression, Vec<Error>> {
        let mut expr = expr.into_inner();
        let lhs = self.get_value(expr.next().unwrap());
        if expr.peek().is_none() {
            Ok(Expression::new(lhs?, None, None))
        } else {
            let op = Operator::from(expr.next().unwrap());
            let rhs = self.get_value(expr.next().unwrap());
            match (lhs, rhs) {
                (Ok(lhs), Ok(rhs)) => Ok(Expression::new(lhs, Some(op), Some(rhs))),
                (x, y) => {
                    let mut errs = Vec::new();
                    if let Some(e) = x.err() { errs.push(e); }
                    if let Some(e) = y.err() { errs.push(e); }
                    Err(errs)
                }
            }
        }
    }

    fn parse_condition(&self, cond: Pair<Rule>) -> Result<Condition, Vec<Error>> {
        let mut cond = cond.into_inner();
        let lhs = self.get_value(cond.next().unwrap());
        let op = Comparator::from(cond.next().unwrap());
        let rhs = self.get_value(cond.next().unwrap());
        match (lhs, rhs) {
            (Ok(lhs), Ok(rhs)) => Ok(Condition::new(lhs, op, rhs)),
            (x, y) => {
                let mut errs = Vec::new();
                if let Some(e) = x.err() { errs.push(e); }
                if let Some(e) = y.err() { errs.push(e); }
                Err(errs)
            }
        }
    }

    fn parse_function_call(&self, call: Pair<Rule>) -> Result<FuncCall, Vec<Error>> {
        let mut parts = call.into_inner();
        let loc = Location::from(parts.peek().unwrap().line_col());
        let func = parts.next().unwrap().as_str().to_owned();

        let args: Vec<_> = parts.next().unwrap().into_inner()
            .map(|decl| self.get_identifier(decl)).collect();
        
        if args.iter().all(|a| a.is_ok()) {
            Ok(FuncCall::new(func, loc, args.into_iter().map(|a| a.unwrap()).collect()))
        } else {
            Err(
                args.into_iter()
                .filter(|a| a.is_err())
                .map(|a| a.err().unwrap())
                .collect()
            )
        }
    }

    fn parse_declarations(&mut self, declarations: Pair<Rule>, use_args: bool) -> Result<(), Vec<Error>> {
        let mut errs = Vec::new();

        for decl in declarations.into_inner() {
            let loc = Location::from(decl.line_col());

            let prev = if self.vars.contains_key(decl.as_str()) {
                self.vars.get(decl.as_str())
            } else {
                None
            };
    
            if let Some(prev) = prev {
                errs.push(Error::new(loc.clone(), "Identifier already declared".to_owned())
                                .add(loc.clone(), format!("Identifier '{}' in line {}", decl.as_str(), loc.row()))
                                .add(prev.loc().clone(), format!("Already declared here in line {}", prev.loc().row())));
            } else {
                let name = decl.as_str().to_owned();
                let ident = Rc::new(Identifier::new(decl.as_str().to_owned(), loc));
    
                if use_args {
                    self.args.push(name.clone());
                    self.vars.insert(name, ident);
                } else {
                    self.vars.insert(name, ident);
                }
            }            
        }

        if !errs.is_empty() {
            Err(errs)
        } else {
            Ok(())
        }
    }

    fn parse_command(&mut self, cmd: Pair<Rule>) -> Result<Command, Vec<Error>> {
        match cmd.as_rule() {
            Rule::cmd_set => {
                let mut parts = cmd.into_inner();
                let ident = self.get_identifier(parts.next().unwrap());
                let expr = self.parse_expression(parts.next().unwrap());
                match (ident, expr) {
                    (Ok(ident), Ok(expr)) => Ok(Command::Set { ident, expr }),
                    (x, y) => {
                        let mut errs = Vec::new();
                        if let Some(e) = x.err() { errs.push(e); }
                        if let Some(e) = y.err() { errs.extend(e); }
                        Err(errs)
                    }
                }
            }

            Rule::cmd_if => {
                let mut parts = cmd.into_inner();
                let cond = self.parse_condition(parts.next().unwrap());
                let then = self.parse_commands(parts.next().unwrap());
                match (cond, then) {
                    (Ok(cond), Ok(then)) => Ok(Command::If { cond, then }),
                    (x, y) => {
                        let mut errs = Vec::new();
                        if let Some(e) = x.err() { errs.extend(e); }
                        if let Some(e) = y.err() { errs.extend(e); }
                        Err(errs)
                    }
                }
            }

            Rule::cmd_if_else => {
                let mut parts = cmd.into_inner();
                let cond = self.parse_condition(parts.next().unwrap());
                let if_true = self.parse_commands(parts.next().unwrap());
                let if_false = self.parse_commands(parts.next().unwrap());
                match (cond, if_true, if_false) {
                    (Ok(cond), Ok(if_true), Ok(if_false)) => Ok(Command::IfElse { cond, if_true, if_false }),
                    (x, y, z) => {
                        let mut errs = Vec::new();
                        if let Some(e) = x.err() { errs.extend(e); }
                        if let Some(e) = y.err() { errs.extend(e); }
                        if let Some(e) = z.err() { errs.extend(e); }
                        Err(errs)
                    }
                }
            }

            Rule::cmd_while => {
                let mut parts = cmd.into_inner();
                let cond = self.parse_condition(parts.next().unwrap());
                let block = self.parse_commands(parts.next().unwrap());
                match (block, cond) {
                    (Ok(block), Ok(cond)) => Ok(Command::While { cond, block }),
                    (x, y) => {
                        let mut errs = Vec::new();
                        if let Some(e) = x.err() { errs.extend(e); }
                        if let Some(e) = y.err() { errs.extend(e); }
                        Err(errs)
                    }
                }
            }

            Rule::cmd_repeat => {
                let mut parts = cmd.into_inner();
                let block = self.parse_commands(parts.next().unwrap());
                let cond = self.parse_condition(parts.next().unwrap());
                match (block, cond) {
                    (Ok(block), Ok(cond)) => Ok(Command::Repeat { cond, block }),
                    (x, y) => {
                        let mut errs = Vec::new();
                        if let Some(e) = x.err() { errs.extend(e); }
                        if let Some(e) = y.err() { errs.extend(e); }
                        Err(errs)
                    }
                }
            }

            Rule::cmd_call => {
                let func = self.parse_function_call(cmd.into_inner().next().unwrap());
                match func {
                    Ok(func) => Ok(Command::Call { func }),
                    Err(errs) => Err(errs),
                }
            }

            Rule::cmd_read => {
                let ident = self.get_identifier(cmd.into_inner().next().unwrap());
                match ident {
                    Ok(ident) => Ok(Command::Read { ident }),
                    Err(err) => Err(vec![err]),
                }
            }

            Rule::cmd_write => {
                let val = self.get_value(cmd.into_inner().next().unwrap());
                match val {
                    Ok(val) => Ok(Command::Write { val }),
                    Err(err) => Err(vec![err]),
                }
            }

            _ => unreachable!(),
        }
    }
    
    fn parse_commands(&mut self, commands: Pair<Rule>) -> Result<Vec<Command>, Vec<Error>> {
        let mut errs = Vec::new();
        let mut cmds = Vec::new();

        for cmd in commands.into_inner() {
            match self.parse_command(cmd) {
                Ok(cmd) => cmds.push(cmd),
                Err(err) => errs.extend(err),
            }
        }

        if !errs.is_empty() {
            Err(errs)
        } else {
            Ok(cmds)
        }
    }

    fn parse_function(name: String, loc: Location, arguments: Option<Pair<Rule>>, function: Pair<Rule>) -> Result<Self, Vec<Error>> {
        let mut fun = Function::new(name, loc);

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
    fn parse_procedure(&mut self, procedure: Pair<Rule>) -> Result<(), Vec<Error>> {
        let mut errs = Vec::new();
        let mut parts = procedure.into_inner();
        let mut head = parts.next().unwrap().into_inner();

        let name = head.next().unwrap();
        let loc = Location::from(name.line_col());
        let name = name.as_str().to_owned();

        if self.procedures.contains_key(&name) {
            let prev = self.procedures.get(&name).unwrap().loc().clone();
            errs.push(Error::new(loc.clone(), "Procedure already declared".to_owned())
                            .add(loc.clone(), format!("Procedure '{}' in line {}", name, loc.row()))
                            .add(prev.clone(), format!("Already declared here in line {}", prev.row())));
        }

        let fun = Function::parse_function(
            name.clone(), loc,
            head.next(),
            parts.next().unwrap(),
        );

        match fun {
            Ok(fun) => { self.procedures.insert(name.clone(), fun); },
            Err(err) => errs.extend(err),
        }

        if errs.is_empty() {
            Ok(())
        } else {
            Err(errs)
        }
    }
    
    fn parse_main(&mut self, main: Pair<Rule>) -> Result<(), Vec<Error>> {
        let loc = Location::from(main.line_col());

        self.main = Function::parse_function(
            "Main".to_owned(), loc,
            None,
            main.into_inner().next().unwrap(),
        )?;

        Ok(())
    }

    fn check_func_call(&self, cmd: &Command, errs: &mut Vec<Error>) {
        match cmd {
            Command::Call { func: caller } => {
                if let Some(called) = self.procedures.get(caller.function_name()) {
                    let expected = called.args_count();
                    let got = caller.args_count();

                    if expected != got {
                        errs.push(
                            Error::new(caller.loc().clone(), "Incorrect argument count".to_owned())
                                  .add(caller.loc().clone(), format!("{} is an incorrect number of arguments for '{}' in line {}", got, caller.function_name(), caller.loc().row()))
                                  .add(called.loc().clone(), format!("The procedure is declared in line {} with {} arguments", called.loc().row(), expected))
                        );
                    }
                } else {
                    errs.push(
                        Error::new(caller.loc().clone(), "Unknown procedure".to_owned())
                              .add(caller.loc().clone(), format!("Unknown procedure '{}'", caller.function_name()))
                    );
                }
            }

            Command::If { cond: _, then } => self.check_func_calls(&then, errs),
            Command::While { cond: _, block } => self.check_func_calls(&block, errs),
            Command::Repeat { cond: _, block } => self.check_func_calls(&block, errs),
            Command::IfElse { cond: _, if_true, if_false } => {
                self.check_func_calls(&if_true, errs);
                self.check_func_calls(&if_false, errs);
            }

            _ => (),
        }
    }

    fn check_func_calls(&self, cmds: &Vec<Command>, errs: &mut Vec<Error>) {
        for cmd in cmds {
            self.check_func_call(cmd, errs);
        }
    }
    
    pub fn parse(input: &str) -> Result<Self, Vec<Error>> {
        let mut program = Program {
            procedures: HashMap::new(),
            main: Function::new("Main".to_owned(), Location::new()),
        };

        let tree = CodeParser::parse(Rule::program_all, input);
        if let Err(err) = tree {
            return Err(vec![Error::from(err)]);
        }
        let tree = tree.unwrap().next().unwrap();
    
        for element in tree.into_inner() {
            match element.as_rule() {
                Rule::procedure => program.parse_procedure(element)?,
                Rule::main => program.parse_main(element)?,
        
                Rule::EOI => (),
                _ => unreachable!(),
            }
        }

        let mut errs = Vec::new();
        program.check_func_calls(&program.main.cmds, &mut errs);
        for proc in program.procedures.values() {
            program.check_func_calls(&proc.cmds, &mut errs);
        }

        // TODO: Generate warnings for unused variables and functions
        // TODO: Generate warnings for variables used before a value is assigned to them

        if errs.is_empty() {
            Ok(program)
        } else {
            Err(errs)
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_ok() {
        let res = Program::parse("PROGRAM IS VAR a, b, c BEGIN a := b + c; END");
        assert!(res.is_ok());
    }

    #[test]
    fn set_undeclared() {
        let res = Program::parse("PROGRAM IS VAR a BEGIN b := c + d; END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(3, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 24)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(1).unwrap();
        assert_eq!(&Location::from((1, 29)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(2).unwrap();
        assert_eq!(&Location::from((1, 33)), e.loc());
        assert_eq!("Undeclared variable", e.msg());
    }

    #[test]
    fn if_ok() {
        let res = Program::parse("PROGRAM IS VAR a, b, c BEGIN IF a > b THEN WRITE c; ENDIF END");
        assert!(res.is_ok());
    }

    #[test]
    fn if_undeclared() {
        let res = Program::parse("PROGRAM IS VAR a BEGIN IF b > c THEN WRITE d; ENDIF END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(3, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 27)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(1).unwrap();
        assert_eq!(&Location::from((1, 31)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(2).unwrap();
        assert_eq!(&Location::from((1, 44)), e.loc());
        assert_eq!("Undeclared variable", e.msg());
    }

    #[test]
    fn if_else_ok() {
        let res = Program::parse("PROGRAM IS VAR a, b, c, d BEGIN IF a > b THEN WRITE c; ELSE WRITE d; ENDIF END");
        assert!(res.is_ok());
    }

    #[test]
    fn if_else_undeclared() {
        let res = Program::parse("PROGRAM IS VAR a BEGIN IF b > c THEN WRITE d; ELSE WRITE e; ENDIF END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(4, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 27)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(1).unwrap();
        assert_eq!(&Location::from((1, 31)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(2).unwrap();
        assert_eq!(&Location::from((1, 44)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(3).unwrap();
        assert_eq!(&Location::from((1, 58)), e.loc());
        assert_eq!("Undeclared variable", e.msg());
    }

    #[test]
    fn while_ok() {
        let res = Program::parse("PROGRAM IS VAR a, b, c BEGIN WHILE a > b DO WRITE c; ENDWHILE END");
        assert!(res.is_ok());
    }

    #[test]
    fn while_undeclared() {
        let res = Program::parse("PROGRAM IS VAR a BEGIN WHILE b > c DO WRITE d; ENDWHILE END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(3, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 45)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(1).unwrap();
        assert_eq!(&Location::from((1, 30)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(2).unwrap();
        assert_eq!(&Location::from((1, 34)), e.loc());
        assert_eq!("Undeclared variable", e.msg());
    }

    #[test]
    fn repeat_ok() {
        let res = Program::parse("PROGRAM IS VAR a, b, c BEGIN REPEAT WRITE c; UNTIL a > b; END");
        assert!(res.is_ok());
    }

    #[test]
    fn repeat_undeclared() {
        let res = Program::parse("PROGRAM IS VAR a BEGIN REPEAT WRITE d; UNTIL b > c; END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(3, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 37)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(1).unwrap();
        assert_eq!(&Location::from((1, 46)), e.loc());
        assert_eq!("Undeclared variable", e.msg());

        let e = err.get(2).unwrap();
        assert_eq!(&Location::from((1, 50)), e.loc());
        assert_eq!("Undeclared variable", e.msg());
    }

    #[test]
    fn read_ok() {
        let res = Program::parse("PROGRAM IS VAR a BEGIN READ a; END");
        assert!(res.is_ok());
    }

    #[test]
    fn read_undeclared() {
        let res = Program::parse("PROGRAM IS VAR a BEGIN READ b; END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(1, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 29)), e.loc());
        assert_eq!("Undeclared variable", e.msg());
    }

    #[test]
    fn write_ok() {
        let res = Program::parse("PROGRAM IS VAR a BEGIN WRITE a; WRITE 1; END");
        assert!(res.is_ok());
    }

    #[test]
    fn write_undeclared() {
        let res = Program::parse("PROGRAM IS VAR a BEGIN WRITE b; END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(1, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 30)), e.loc());
        assert_eq!("Undeclared variable", e.msg());
    }

    #[test]
    fn procedures_ok() {
        let res = Program::parse("PROCEDURE foo(x) IS VAR a BEGIN a := x; WRITE x; END PROCEDURE bar(x) IS VAR a BEGIN a := x; WRITE x; END PROGRAM IS VAR a BEGIN foo(a); bar(a); END");
        assert!(res.is_ok());
    }

    #[test]
    fn procedures_redeclared() {
        let res = Program::parse("PROCEDURE foo(x) IS VAR a BEGIN a := x; WRITE x; END PROCEDURE foo(x) IS VAR a BEGIN a := x; WRITE x; END PROGRAM IS VAR a BEGIN foo(a); bar(a); END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(1, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 64)), e.loc());
        assert_eq!("Procedure already declared", e.msg());
    }

    #[test]
    fn args_ok() {
        let res = Program::parse("PROCEDURE foo(x, y, z) IS VAR a BEGIN a := x; WRITE x; END PROGRAM IS VAR a, b, c BEGIN foo(a, b, c); END");
        assert!(res.is_ok());
    }

    #[test]
    fn args_redeclared() {
        let res = Program::parse("PROCEDURE foo(x, y, y) IS VAR a BEGIN a := x; WRITE x; END PROGRAM IS VAR a, b, c BEGIN foo(a, b, c); END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(1, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 21)), e.loc());
        assert_eq!("Identifier already declared", e.msg());
    }

    #[test]
    fn vars_ok() {
        let res = Program::parse("PROGRAM IS VAR a, b, c BEGIN WRITE a; END");
        assert!(res.is_ok());
    }

    #[test]
    fn vars_redeclared() {
        let res = Program::parse("PROGRAM IS VAR a, b, b BEGIN WRITE a; END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(1, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 22)), e.loc());
        assert_eq!("Identifier already declared", e.msg());
    }

    #[test]
    fn vars_args_ok() {
        let res = Program::parse("PROCEDURE foo(x, y, z) IS VAR a, b, c BEGIN a := x; WRITE x; END PROGRAM IS VAR a, b, c BEGIN foo(a, b, c); END");
        assert!(res.is_ok());
    }

    #[test]
    fn vars_args_redeclared() {
        let res = Program::parse("PROCEDURE foo(x, y, z) IS VAR a, b, x BEGIN a := x; WRITE x; END PROGRAM IS VAR a, b, c BEGIN foo(a, b, c); END");
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(1, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((1, 37)), e.loc());
        assert_eq!("Identifier already declared", e.msg());
    }

    #[test]
    fn call_ok() {
        let res = Program::parse("PROCEDURE foo(x) IS BEGIN WRITE x; END PROGRAM IS VAR a BEGIN foo(a); IF a > 2 THEN foo(a); ENDIF END");
        assert!(res.is_ok());
    }

    #[test]
    fn call_undeclared() {
        let program = "\
            PROCEDURE foo(x) IS\n\
            BEGIN\n    \
                WRITE x;\n\
            END\n\n\
            PROGRAM IS VAR\n    \
                a, b\n\
            BEGIN\n    \
                bar(a);\n    \
                IF a > 2 THEN\n        \
                    foo(a, b);\n    \
                ENDIF\n\
            END";

        let res = Program::parse(program);
        assert!(res.is_err());

        let err = res.err().unwrap();
        assert_eq!(2, err.len());

        let e = err.get(0).unwrap();
        assert_eq!(&Location::from((9, 5)), e.loc());
        assert_eq!("Unknown procedure", e.msg());

        let e = err.get(1).unwrap();
        assert_eq!(&Location::from((11, 9)), e.loc());
        assert_eq!("Incorrect argument count", e.msg());
    }

    // TODO: Better *_ok tests
}
