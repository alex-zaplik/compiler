use crate::ast::Location;

#[derive(Debug)]
struct ErrorStep {
    msg: String,
    loc: Location,
}

impl ErrorStep {
    fn format_with(&self, path: &str, input: &str) -> String {
        let spacing = format!("{}", self.loc.row()).len();
        format!(
            "{s} > {path}:{r}:{c}:\n\
             {s} | \n\
             {r} | {line}\n\
             {s} | {ms}^\n\
             {s} | {ms}{message}\n",
            r = self.loc.row(),
            c = self.loc.col(),
            s = " ".repeat(spacing),
            ms = " ".repeat(self.loc.col()),
            line = input.lines().nth(self.loc.row() - 1).unwrap(),
            message = self.msg,
        )
    }
}

#[derive(Debug)]
pub struct Error {
    steps: Vec<ErrorStep>,
    loc: Location,
    msg: String,
}

impl Error {
    pub fn new(loc: Location, msg: String) -> Self {
        Self { steps: Vec::new(), loc, msg }
    }

    pub fn add(mut self, loc: Location, msg: String) -> Self {
        self.steps.push(ErrorStep { msg, loc });
        self
    }

    pub fn format_with(&self, path: &str, input: &str) -> String {
        let mut msg = format!(
            "{message} at {path}:{r}:{c}:\n",
            message = self.msg,
            r = self.loc.row(),
            c = self.loc.col(),
        );

        for step in &self.steps {
            msg.push_str(step.format_with(path, input).as_str());
        }

        msg
    }

    pub fn msg(&self) -> &str {
        &self.msg
    }

    pub fn loc(&self) -> &Location {
        &self.loc
    }
}

impl From<Error> for Vec<Error> {
    fn from(value: Error) -> Self {
        vec![value]
    }
}
