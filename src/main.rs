mod parser;
mod expr;

use argmin::{core::{CostFunction, Executor, State, observers::{Observe, ObserverMode}}, solver::simulatedannealing::{Anneal, SimulatedAnnealing}};
use expr::Statement;
use parser::parse;

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

struct Logger;

impl<I: State<Param = Statement>> Observe<I> for Logger {
    fn observe_iter(&mut self, state: &I, _kv: &argmin::core::KV) -> Result<(), argmin::core::Error> {
        print!("{} ({}) | ", state.get_best_param().unwrap(), state.get_best_cost());
        println!("{} ({})", state.get_param().unwrap(), state.get_cost());
        Ok(())
    }
}

fn main() {
    let initial = parse(b"A | A | B").unwrap();
    let problem = BooleanProblem::new(&initial);
    let observer = Logger;
    let solver = SimulatedAnnealing::new(100.0)
        .unwrap()
        .with_reannealing_accepted(100);
    let result = Executor::new(problem, solver)
        .add_observer(observer, ObserverMode::Always)
        .configure(|state| state.max_iters(1000).param(initial))
        .run()
        .expect("Failed to optimize");

    let best = result.state().get_best_param().unwrap();

    println!("{best}");
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
