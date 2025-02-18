mod parser;
mod expr;

use std::{fs, path::PathBuf, sync::mpsc::channel};
use clap::{Parser, Subcommand};
use argmin::{core::{CostFunction, Executor, State, observers::{Observe, ObserverMode}}, solver::simulatedannealing::{Anneal, SimulatedAnnealing}};
use expr::Statement;
use parser::{Result as PResult, parse};

struct BooleanProblem {
    table: Box<[bool]>,
    vars: Box<[u8]>,
}

impl BooleanProblem {
    fn new(statement: &Statement) -> Self {
        let vars = statement.get_vars();
        let table = statement.generate_truth_table(&vars);

        Self { table, vars }
    }

    fn verify(&self, statement: &Statement) {
        statement.sanity_check();
        assert_eq!(self.table, statement.generate_truth_table(&self.vars));
    }
}

impl CostFunction for BooleanProblem {
    type Param = Statement;
    type Output = f64;

    fn cost(&self, param: &Self::Param) -> Result<Self::Output, argmin::core::Error> {
        Ok(param.size() as f64)
    }
}

impl Anneal for BooleanProblem {
    type Param = Statement;
    type Output = Statement;
    type Float = f64;

    fn anneal(&self, param: &Self::Param, _extent: Self::Float) -> Result<Self::Output, argmin::core::Error> {
        let mut output = param.clone();
        let mut fns = Statement::EQUIVALENCES.clone();

        fastrand::shuffle(&mut fns);

        for f in fns {
            if output.try_apply(f) {
                return Ok(output);
            }
        }

        eprintln!("[WARN] No rules applicable");
        Ok(output)
    }
}

struct Logger {
    worker: usize,
}

impl<I: State<Param = Statement>> Observe<I> for Logger {
    fn observe_iter(&mut self, state: &I, _kv: &argmin::core::KV) -> Result<(), argmin::core::Error> {
        println!("[WORKER {}]\tBest size: {}", self.worker, state.get_best_cost());
        Ok(())
    }

    fn observe_final(&mut self, state: &I) -> Result<(), argmin::core::Error> {
        println!("[WORKER {}]\tBest: {} (size = {})", self.worker, state.get_best_param().unwrap(), state.get_best_cost());
        Ok(())
    }
}

const RESET_ATTEMPTS: usize = 100;
const WORKERS: usize = 12;

#[derive(Parser)]
#[command(about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Simplify { expr: String },
    Decide { path: PathBuf },
}

fn read_argument(path: PathBuf) -> PResult<Statement> {
    let string = fs::read_to_string(path).unwrap();
    let lines = string.lines().collect::<Vec<_>>();
    let mut argument = String::new();

    let (conclusion, lines) = lines.split_last().expect("Empty argument file");

    for line in lines {
        argument.push('(');
        argument.push_str(line);
        argument.push_str(")&");
    }

    argument.push_str("~(");
    argument.push_str(conclusion);
    argument.push(')');

    parse(dbg!(argument).as_bytes())
}

fn main() {
    let mut statement = match Cli::parse().command {
        Commands::Simplify { expr } => parse(expr.as_bytes()).unwrap(),
        Commands::Decide { path } => read_argument(path).unwrap(),
    };

    for _ in 0..RESET_ATTEMPTS {
        let (tx, rx) = channel::<Statement>();
        let statement_ref = &statement;

        rayon::scope(move |s| {
            for i in 0..WORKERS {
                let tx = tx.clone();
                s.spawn(move |_| {
                    let solver = SimulatedAnnealing::new(100.0)
                        .unwrap()
                        .with_reannealing_best(2000)
                        .with_stall_best(1000000)
                        .with_reannealing_accepted(1000);

                    let result = Executor::new(BooleanProblem::new(statement_ref), solver)
                        .add_observer(Logger { worker: i }, ObserverMode::NewBest)
                        .configure(|state| state.param(statement_ref.clone()))
                        .run()
                        .expect("Failed to optimize");

                    let best = result.state().get_best_param().unwrap().clone();
                    result.problem.problem.unwrap().verify(&best);
                    tx.send(best).unwrap();
                });
            }
        });

        statement = rx.iter().min_by_key(|s| s.size()).unwrap();
    }

}

#[cfg(test)]
mod tests {
    use crate::{parser::parse, expr::Statement};

    const TEST_ITERS: usize = 1000;

    #[test]
    fn monte_carlo_test() {
        let mut statement = parse(b"A & ~A").unwrap();
        let vars = statement.get_vars();
        let original_table = statement.generate_truth_table(&vars);

        let mut usage_tracker = [0; Statement::EQUIVALENCES.len()];
        let mut attempts = 0;
        let mut fns = Statement::EQUIVALENCES.iter().enumerate().collect::<Box<[_]>>();

        for iter in 0..TEST_ITERS {
            let node = statement.next();

            fastrand::shuffle(&mut fns);

            for (i, equiv) in fns.iter() {
                if equiv(&mut statement, node) {
                    println!("{} {}", iter, statement.any_fraction());
                    statement.sanity_check();
                    usage_tracker[*i] += 1;
                    assert_eq!(original_table, statement.generate_truth_table(&vars));
                    break;
                }
                else {
                    attempts += 1;
                }
            }
        }

        println!("Applied {} out of {attempts}", usage_tracker.iter().sum::<usize>());

        for (name, count) in Statement::EQUIVALENCE_NAMES.iter().zip(usage_tracker.iter()) {
            println!("{count}\t{name}");
        }
    }
}
