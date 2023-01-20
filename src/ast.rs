use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug)]
pub struct Identifier {
    name: String,
    row: usize,
    col: usize,
}

impl Identifier {
    pub fn new(name: String, row: usize, col: usize) -> Self {
        Self { name, row, col }
    }

    pub fn row(&self) -> usize {
        self.row
    }

    pub fn col(&self) -> usize {
        self.row
    }
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

#[derive(Debug)]
pub struct FuncCall {
    func: String,
    args: Vec<Rc<Identifier>>,
    row: usize,
    col: usize,
}

impl FuncCall {
    pub fn new(func: String, row: usize, col: usize, args: Vec<Rc<Identifier>>) -> Self {
        Self { func, row, col, args }
    }

    pub fn args_count(&self) -> usize {
        self.args.len()
    }

    pub fn function_name(&self) -> &String {
        &self.func
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

impl Expression {
    pub fn new(lhs: Value, op: Option<Operator>, rhs: Option<Value>) -> Self {
        Self { lhs, op, rhs }
    }
}

#[derive(Debug)]
pub struct Condition {
    lhs: Value,
    rhs: Value,
    op: Comparator,
}

impl Condition {
    pub fn new(lhs: Value, op: Comparator, rhs: Value) -> Self {
        Self { lhs, op, rhs }
    }
}

#[derive(Debug)]
pub enum Command {
    Set { ident: Rc<Identifier>, expr: Expression },
    Read { ident: Rc<Identifier> },
    Write { val: Value },
    If { cond: Condition, then: Vec<Command> },
    IfElse { cond: Condition, if_true: Vec<Command>, if_false: Vec<Command> },
    While { cond: Condition, block: Vec<Command> },
    Repeat { cond: Condition, block: Vec<Command> },
    Call { func: FuncCall },
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub args: HashMap<String, Rc<Identifier>>,
    pub vars: HashMap<String, Rc<Identifier>>,
    pub cmds: Vec<Command>,
    col: usize,
    row: usize,
}

impl Function {
    pub fn new(name: String, col: usize, row: usize) -> Self {
        Self {
            name, col, row,
            args: HashMap::new(),
            vars: HashMap::new(),
            cmds: Vec::new(),
        }
    }

    pub fn args_count(&self) -> usize {
        self.args.len()
    }

    pub fn row(&self) -> usize {
        self.row
    }

    pub fn col(&self) -> usize {
        self.row
    }
}

#[derive(Debug)]
pub struct Program {
    pub procedures: HashMap<String, Function>,
    pub main: Function,
}
