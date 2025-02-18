use std::result;
use crate::expr::{ Statement, Expr, ExprRef };

pub type Result<T> = result::Result<T, String>;

struct Parser<'a> {
    source: &'a [u8],
    index: usize,
    current: u8,
    exprs: Vec<Expr>,
}

impl<'a> Parser<'a> {
    fn new(source: &'a [u8]) -> Self {
        Self { source, index: 0, current: source[0], exprs: Vec::new() }
    }

    fn expr(&mut self) -> Result<ExprRef> {
        self.disjunction()
    }

    fn disjunction(&mut self) -> Result<ExprRef> {
        let mut expr = self.conjunction()?;

        loop {
            self.skip_whitespace();

            if self.current == b'|' {
                self.advance();
                let rhs = self.conjunction()?;
                expr = self.create_disjunction(expr, rhs);
            }
            else {
                break;
            }
        }

        Ok(expr)
    }

    fn conjunction(&mut self) -> Result<ExprRef> {
        let mut expr = self.term()?;

        loop {
            self.skip_whitespace();

            if self.current == b'&' {
                self.advance();
                let rhs = self.term()?;
                expr = self.create_conjunction(expr, rhs);
            }
            else {
                break;
            }
        }

        Ok(expr)
    }

    fn term(&mut self) -> Result<ExprRef> {
        self.skip_whitespace();

        match self.advance() {
            b'^' => Ok(self.create_tautology()),
            b'?' => Ok(self.create_contradiction()),

            b'~' => {
                let oprand = self.term()?;
                Ok(self.create_negation(oprand))
            }

            b'(' => {
                let result = self.expr()?;
                self.skip_whitespace();

                if self.current == b')' {
                    self.advance();
                    Ok(result)
                }
                else {
                    Err(format!("Expected a ')' but found '{}'", self.current))
                }
            }

            c if c.is_ascii_alphabetic() => Ok(self.create_atomic(c)),

            b'\0' => Err("Expected an expression but found nothing.".to_owned()),
            _ => Err(format!("Invalid byte '{}'", self.current)),
        }
    }

    fn skip_whitespace(&mut self) {
        while self.current.is_ascii_whitespace() {
            self.advance();
        }
    }

    fn advance(&mut self) -> u8 {
        let old = self.current;
        self.index += 1;
        self.current = *self.source.get(self.index).unwrap_or(&b'\0');
        old
    }

    fn create_tautology(&mut self) -> ExprRef {
        self.exprs.push(Expr::tautology());
        self.exprs.len() - 1
    }

    fn create_contradiction(&mut self) -> ExprRef {
        self.exprs.push(Expr::contradiction());
        self.exprs.len() - 1
    }

    fn create_atomic(&mut self, c: u8) -> ExprRef {
        self.exprs.push(Expr::atomic(c));
        self.exprs.len() - 1
    }

    fn create_negation(&mut self, oprand: ExprRef) -> ExprRef {
        self.exprs.push(Expr::negation(oprand));
        self.exprs.len() - 1
    }

    fn create_conjunction(&mut self, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
        self.exprs.push(Expr::conjunction(lhs, rhs));
        self.exprs.len() - 1
    }

    fn create_disjunction(&mut self, lhs: ExprRef, rhs: ExprRef) -> ExprRef {
        self.exprs.push(Expr::disjunction(lhs, rhs));
        self.exprs.len() - 1
    }
}

pub fn parse(source: &[u8]) -> Result<Statement>  {
    let mut parser = Parser::new(source);
    let root = parser.expr()?;
    Ok(Statement::new(root, parser.exprs))
}
