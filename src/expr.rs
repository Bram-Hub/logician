use std::fmt::{Display, self};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExprKind {
    Free(Option<ExprRef>),

    Any,

    Tautology,
    Contradiction,
    Atomic(u8),
    Negation,
    Conjunction,
    Disjunction,
}

impl ExprKind {
    fn get_dual(self) -> Self {
        match self {
            Self::Conjunction => Self::Disjunction,
            Self::Disjunction => Self::Conjunction,
            Self::Tautology => Self::Contradiction,
            Self::Contradiction => Self::Tautology,
            _ => unreachable!(),
        }
    }

    fn is_operation(self) -> bool {
        match self {
            Self::Conjunction | Self::Disjunction | Self::Negation => true,
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Expr {
    kind: ExprKind,
    a: ExprRef,
    b: ExprRef,
}

impl Expr {
    fn new(kind: ExprKind, a: ExprRef, b: ExprRef) -> Self {
        Self { kind, a, b }
    }

    pub fn tautology() -> Self {
        Self::new(ExprKind::Tautology, 0, 0)
    }

    pub fn contradiction() -> Self {
        Self::new(ExprKind::Contradiction, 0, 0)
    }

    pub fn atomic(symbol: u8) -> Self {
        Self::new(ExprKind::Atomic(symbol), 0, 0)
    }

    pub fn negation(a: ExprRef) -> Self {
        Self::new(ExprKind::Negation, a, 0)
    }

    pub fn conjunction(a: ExprRef, b: ExprRef) -> Self {
        Self::new(ExprKind::Conjunction, a, b)
    }

    pub fn disjunction(a: ExprRef, b: ExprRef) -> Self {
        Self::new(ExprKind::Disjunction, a, b)
    }
}

pub type ExprRef = usize;

#[derive(Clone)]
pub struct Statement {
    root: ExprRef,
    exprs: Vec<Expr>,
    free_list: Option<ExprRef>,
    tree_size: usize,
}

impl Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn format_node(node: ExprRef, exprs: &[Expr]) -> String  {
            match exprs[node].kind {
                ExprKind::Tautology => "^".to_owned(),
                ExprKind::Contradiction => "?".to_owned(),
                ExprKind::Atomic(c) => (c as char).to_string(),
                ExprKind::Negation => format!("~{}", format_node(exprs[node].a, exprs)),
                ExprKind::Conjunction => format!("({}&{})", format_node(exprs[node].a, exprs), format_node(exprs[node].b, exprs)),
                ExprKind::Disjunction => format!("({}|{})", format_node(exprs[node].a, exprs), format_node(exprs[node].b, exprs)),

                ExprKind::Any => "*".to_owned(),

                ExprKind::Free(_) => unreachable!(),
            }
        }

        write!(f, "{}", format_node(self.root, &self.exprs))
    }
}

impl Statement {
    pub fn new(root: ExprRef, exprs: Vec<Expr>) -> Self {
        let tree_size = exprs.len();
        Self { root, exprs, free_list: None, tree_size }
    }

    // pub fn locate(&self, locator: &str) -> ExprRef {
    //     let mut node = self.root;

    //     for c in locator.bytes() {
    //         let expr = self.exprs[node];

    //         node = match c {
    //             b'<' => { assert!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction); expr.a }
    //             b'>' => { assert!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction); expr.b }
    //             b'v' => { assert!(expr.kind == ExprKind::Negation); expr.a }
    //             _ => panic!("Invalid character in locator"),
    //         };
    //     }

    //     node
    // }

    // pub fn next(&mut self) -> ExprRef {
    //     let mut cursor = fastrand::usize(0..self.exprs.len());
    //     let mut first = true;

    //     let start = cursor;

    //     loop {
    //         assert!(first || cursor != start);

    //         if let ExprKind::Free(_) = self.exprs[cursor].kind {
    //             cursor += 1;
    //             cursor %= self.exprs.len();
    //             first = false;

    //             continue;
    //         }

    //         return cursor;
    //     }
    // }

    pub fn try_apply(&mut self, f: fn (&mut Self, ExprRef) -> bool) -> bool {
        let mut cursor = fastrand::usize(0..self.exprs.len());
        let mut first = true;

        let start = cursor;

        loop {
            let node = cursor;

            if !first && cursor == start {
                return false;
            }

            first = false;
            cursor += 1;
            cursor %= self.exprs.len();

            if let ExprKind::Free(_) = self.exprs[node].kind {
                continue;
            }

            if f(self, node) {
                return true;
            }
        }
    }

    pub fn size(&self) -> usize {
        // self.tree_size
        self.exprs.iter().filter(|e| e.kind.is_operation()).count()
    }

    // pub fn usage(&self) -> f64 {
    //     self.size() as f64 / self.exprs.len() as f64
    // }

    // pub fn any_fraction(&self) -> f64 {
    //     self.exprs.iter().filter(|e| e.kind == ExprKind::Any).count() as f64 / self.exprs.len() as f64
    // }

    pub fn get_vars(&self) -> Box<[u8]> {
        let mut vars = self.exprs.iter().filter_map(|e| if let ExprKind::Atomic(c) = e.kind { Some(c) } else { None }).collect::<Vec<_>>();

        vars.sort_unstable();
        vars.dedup();
        vars.into_boxed_slice()
    }

    pub fn generate_truth_table(&self, vars: &[u8]) -> Box<[bool]> {
        let mut context = vars.iter().map(|&c| (c, false)).collect::<Box<[_]>>();
        let mut table = Vec::with_capacity(context.len());

        for _ in 0 .. 1 << context.len() {
            table.push(self.evaluate(self.root, &context));

            // println!("{} {}: {}", context.iter().map(|&(a, b)| format!("{}:
            // {}", a as char, b as u8)).collect::<Vec<_>>().join("\t"),
            // self.format_str(), *table.last().unwrap() as u8);

            for x in context.iter_mut() {
                x.1 = !x.1;
                if x.1 { break; }
            }
        }

        table.into_boxed_slice()
    }

    fn evaluate(&self, node: ExprRef, context: &[(u8, bool)]) -> bool {
        let expr = self.exprs[node];

        match expr.kind {
            ExprKind::Any => false,
            ExprKind::Contradiction => false,
            ExprKind::Tautology => true,
            ExprKind::Atomic(a) => context.iter().filter(|c| c.0 == a).next().unwrap().1,
            ExprKind::Conjunction => self.evaluate(expr.a, context) && self.evaluate(expr.b, context),
            ExprKind::Disjunction => self.evaluate(expr.a, context) || self.evaluate(expr.b, context),
            ExprKind::Negation => !self.evaluate(expr.a, context),
            ExprKind::Free(_) => unreachable!(),
        }
    }

    fn assert_binary(&mut self, node: ExprRef, kind: ExprKind) -> bool {
        let expr = self.exprs[node];

        match expr.kind {
            ExprKind::Free(_) => unreachable!(),
            ExprKind::Any => {
                self.exprs[node].kind = kind;
                self.exprs[node].a = self.expr_new(ExprKind::Any, 0, 0);
                self.exprs[node].b = self.expr_new(ExprKind::Any, 0, 0);

                true
            }

            k => k == kind,
        }
    }

    fn assert_negation(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];

        match expr.kind {
            ExprKind::Free(_) => unreachable!(),
            ExprKind::Negation => true,
            ExprKind::Any => {
                self.exprs[node].kind = ExprKind::Negation;
                self.exprs[node].a = self.expr_new(ExprKind::Any, 0, 0);

                true
            }

            _ => false,
        }
    }

    // fn assert_atomic(&mut self, node: ExprRef, kind: ExprKind) -> bool {
    //     let expr = self.exprs[node];

    //     match expr.kind {
    //         ExprKind::Free(_) => unreachable!(),
    //         ExprKind::Any => {
    //             self.exprs[node].kind = kind;
    //             true
    //         }

    //         k => k == kind,
    //     }
    // }

    fn order_eq_exprs(&mut self, a: ExprRef, b: ExprRef) -> Option<(ExprRef, ExprRef)> {
        let expr_a = self.exprs[a];
        let expr_b = self.exprs[b];

        match (expr_a.kind, expr_b.kind) {
            (ExprKind::Any, ExprKind::Any) => None,
            (ExprKind::Any, _) => Some((b, a)),
            (_, ExprKind::Any) => Some((a, b)),
            (_, _) => if self.expr_eq(a, b) { Some((a, b)) } else { None }
        }
    }

    fn expr_eq(&self, a: ExprRef, b: ExprRef) -> bool {
        let expr_a = self.exprs[a];
        let expr_b = self.exprs[b];

        if expr_a.kind == ExprKind::Any || expr_b.kind == ExprKind::Any {
            return true;
        }

        if expr_a.kind != expr_b.kind {
            return false;
        }

        match expr_a.kind {
            ExprKind::Negation => self.expr_eq(expr_a.a, expr_b.a),
            ExprKind::Conjunction | ExprKind::Disjunction => self.expr_eq(expr_a.a, expr_b.a) && self.expr_eq(expr_a.b, expr_b.b),
            _ => true,
        }
    }

    fn expr_copy(&mut self, node: ExprRef) -> ExprRef {
        let expr = self.exprs[node];

        match expr.kind {
            ExprKind::Free(_) => unreachable!(),
            ExprKind::Atomic(_) | ExprKind::Contradiction | ExprKind::Tautology | ExprKind::Any => self.expr_new(expr.kind, 0, 0),
            ExprKind::Negation => {
                let a = self.expr_copy(expr.a);
                self.expr_new(expr.kind, a, 0)
            },
            ExprKind::Conjunction | ExprKind::Disjunction => {
                let a = self.expr_copy(expr.a);
                let b = self.expr_copy(expr.b);
                self.expr_new(expr.kind, a, b)
            },
        }
    }

    fn expr_free(&mut self, node: ExprRef) {
        self.tree_size -= 1;
        self.exprs[node].kind = ExprKind::Free(self.free_list);
        self.free_list = Some(node);
    }

    fn expr_delete(&mut self, node: ExprRef) {
        let expr = self.exprs[node];
        self.expr_free(node);

        match expr.kind {
            ExprKind::Free(_) => unreachable!(),
            ExprKind::Atomic(_) | ExprKind::Contradiction | ExprKind::Tautology | ExprKind::Any => (),
            ExprKind::Negation => self.expr_delete(expr.a),
            ExprKind::Conjunction | ExprKind::Disjunction => {
                self.expr_delete(expr.a);
                self.expr_delete(expr.b);
            },
        }
    }

    fn expr_new(&mut self, kind: ExprKind, a: ExprRef, b: ExprRef) -> ExprRef {
        self.tree_size += 1;

        match self.free_list {
            Some(node) => {
                let ExprKind::Free(next) = self.exprs[node].kind else { unreachable!(); };
                self.free_list = next;
                self.exprs[node] = Expr { kind, a, b };
                node
            }

            None => {
                self.exprs.push(Expr { kind, a, b });
                self.exprs.len() - 1
            }
        }
    }

    pub fn sanity_check(&self) {
        let mut reachable = vec![false; self.exprs.len()];

        assert_eq!(self.tree_size, self.exprs.iter().filter(|e| if let ExprKind::Free(_) = e.kind { false } else { true }).count());

        let mut to_check = vec![self.root];
        while let Some(node) = to_check.pop() {
            let expr = self.exprs[node];

            reachable[node] = true;

            match expr.kind {
                ExprKind::Tautology | ExprKind::Contradiction | ExprKind::Atomic(_) | ExprKind::Any => (),
                ExprKind::Negation => to_check.push(expr.a),
                ExprKind::Conjunction | ExprKind::Disjunction => { to_check.push(expr.a); to_check.push(expr.b); },
                ExprKind::Free(_) => assert!(false, "Free node reached from expr root"),
            }
        }

        let mut head = self.free_list;
        while let Some(node) = head {
            let expr = self.exprs[node];

            reachable[node] = true;

            match expr.kind {
                ExprKind::Free(next) => head = next,
                _ => assert!(false, "Expr found in free list"),
            }
        }

        for (i, c) in reachable.into_iter().enumerate() {
            assert!(c, "{:?} was unreachable", self.exprs[i]);
        }
    }
}

macro_rules! ensure {
    ($condition:expr) => {
        if !($condition) {
            // eprintln!("Could not satisfy {}", stringify!($condition));
            return false;
        }
    };
}

macro_rules! build_tables {
    ($length:expr; $($name:ident),+ $(,)?) => {
        pub const EQUIVALENCES: [fn (&mut Self, ExprRef) -> bool; $length] = [
            $(Self::$name),+
        ];

        // pub const EQUIVALENCE_NAMES: [&'static str; $length] = [
        //     $(stringify!($name)),+
        // ];
    };
}

impl Statement {
    build_tables!(23;
        fwd_association,
        inv_association,
        commutation,
        fwd_idempotence,
        inv_con_idempotence,
        inv_dis_idempotence,
        fwd_demorgans,
        inv_demorgans,
        fwd_distribution,
        inv_distribution,
        fwd_double_negation,
        inv_double_negation,
        fwd_complement,
        // inv_complement,
        fwd_identity,
        inv_con_identity,
        inv_dis_identity,
        fwd_annihilation,
        // inv_annihilation,
        fwd_inverse,
        inv_inverse,
        fwd_absorption,
        // inv_con_absorption,
        // inv_dis_absorption,
        fwd_reduction,
        inv_reduction,
        fwd_adjacency,
        // inv_con_adjacency,
        // inv_dis_adjacency,
    );

    pub fn fwd_association(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);
        ensure!(self.assert_binary(expr.b, expr.kind));

        let rhs = self.exprs[expr.b];

        self.exprs[node].a = expr.b;
        self.exprs[node].b = rhs.b;
        self.exprs[expr.b].a = expr.a;
        self.exprs[expr.b].b = rhs.a;

        true
    }

    pub fn inv_association(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);
        ensure!(self.assert_binary(expr.a, expr.kind));

        let lhs = self.exprs[expr.a];

        self.exprs[node].b = expr.a;
        self.exprs[node].a = lhs.a;
        self.exprs[expr.a].a = lhs.b;
        self.exprs[expr.a].b = expr.b;

        true
    }

    pub fn commutation(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);

        self.exprs[node].a = expr.b;
        self.exprs[node].b = expr.a;

        true
    }

    pub fn fwd_idempotence(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);
        let Some((a, b)) = self.order_eq_exprs(expr.a, expr.b) else { return false };

        self.exprs[node] = self.exprs[a];

        self.expr_free(a);
        self.expr_delete(b);

        true
    }

    pub fn inv_con_idempotence(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];

        let a = self.expr_new(expr.kind, expr.a, expr.b);
        let b = self.expr_copy(a);

        self.exprs[node] = Expr { kind: ExprKind::Conjunction, a, b };

        true
    }

    pub fn inv_dis_idempotence(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];

        let a = self.expr_new(expr.kind, expr.a, expr.b);
        let b = self.expr_copy(a);

        self.exprs[node] = Expr { kind: ExprKind::Disjunction, a, b };

        true
    }

    pub fn fwd_demorgans(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Negation);
        ensure!(self.assert_binary(expr.a, ExprKind::Conjunction) || self.assert_binary(expr.a, ExprKind::Disjunction));

        let bin_op = self.exprs[expr.a];
        let dual_kind = bin_op.kind.get_dual();

        let negation = self.expr_new(ExprKind::Negation, bin_op.b, 0);

        self.exprs[expr.a].kind = ExprKind::Negation;
        self.exprs[node] = Expr::new(dual_kind, expr.a, negation);

        true
    }

    pub fn inv_demorgans(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);
        ensure!(self.assert_negation(expr.a) && self.assert_negation(expr.b));

        // let lhs = self.exprs[expr.a];
        let rhs = self.exprs[expr.b];
        let dual_kind = expr.kind.get_dual();

        self.exprs[node].kind = ExprKind::Negation;
        self.exprs[expr.a].kind = dual_kind;
        self.exprs[expr.a].b = rhs.a;
        self.expr_free(expr.b);

        true
    }

    pub fn fwd_distribution(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);

        let dual_kind = expr.kind.get_dual();
        ensure!(self.assert_binary(expr.b, dual_kind));
        // let rhs = self.exprs[expr.b];

        let lhs_copy = self.expr_copy(expr.a);
        let binary = self.expr_new(expr.kind, expr.a, self.exprs[expr.b].a);

        self.exprs[node].a = binary;
        self.exprs[expr.b].a = lhs_copy;
        self.exprs[expr.b].kind = expr.kind;
        self.exprs[node].kind = dual_kind;

        true
    }

    pub fn inv_distribution(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);

        let dual_kind = expr.kind.get_dual();
        ensure!(self.assert_binary(expr.a, dual_kind) && self.assert_binary(expr.b, dual_kind));
        let lhs = self.exprs[expr.a];
        let rhs = self.exprs[expr.b];
        let Some((a, b)) = self.order_eq_exprs(lhs.a, rhs.a) else { return false };

        self.expr_delete(b);
        self.expr_free(expr.a);

        self.exprs[node].a = a;
        self.exprs[expr.b].a = lhs.b;
        self.exprs[node].kind = dual_kind;
        self.exprs[expr.b].kind = expr.kind;

        true
    }

    pub fn fwd_double_negation(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Negation);

        let oprand = self.exprs[expr.a];
        ensure!(oprand.kind == ExprKind::Negation);

        self.exprs[node] = self.exprs[oprand.a];

        self.expr_free(expr.a);
        self.expr_free(oprand.a);

        true
    }

    pub fn inv_double_negation(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        let inner = self.expr_new(expr.kind, expr.a, expr.b);
        let negation = self.expr_new(ExprKind::Negation, inner, 0);

        self.exprs[node].kind = ExprKind::Negation;
        self.exprs[node].a = negation;

        true
    }

    pub fn fwd_complement(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);

        // let lhs = self.exprs[expr.a];
        let rhs = self.exprs[expr.b];
        ensure!(rhs.kind == ExprKind::Negation);
        ensure!(self.expr_eq(expr.a, rhs.a));

        self.exprs[node].kind = match expr.kind {
            ExprKind::Conjunction => ExprKind::Contradiction,
            ExprKind::Disjunction => ExprKind::Tautology,
            _ => unreachable!(),
        };

        self.expr_delete(expr.a);
        self.expr_delete(expr.b);

        true
    }

    // pub fn inv_complement(&mut self, node: ExprRef) -> bool {
    //     let expr = self.exprs[node];
    //     ensure!(expr.kind == ExprKind::Contradiction || expr.kind == ExprKind::Tautology);

    //     self.exprs[node].kind = match expr.kind {
    //         ExprKind::Contradiction => ExprKind::Conjunction,
    //         ExprKind::Tautology => ExprKind::Disjunction,
    //         _ => unreachable!(),
    //     };

    //     let inner = self.expr_new(ExprKind::Any, 0, 0);
    //     self.exprs[node].a = self.expr_new(ExprKind::Any, 0, 0);
    //     self.exprs[node].b = self.expr_new(ExprKind::Negation, inner, 0);

    //     true
    // }

    pub fn fwd_identity(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);

        let rhs = self.exprs[expr.b];
        ensure!(rhs.kind == match expr.kind {
            ExprKind::Conjunction => ExprKind::Tautology,
            ExprKind::Disjunction => ExprKind::Contradiction,
            _ => unreachable!(),
        });

        self.exprs[node] = self.exprs[expr.a];

        self.expr_free(expr.a);
        self.expr_free(expr.b);

        true
    }

    pub fn inv_con_identity(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        let a = self.expr_new(expr.kind, expr.a, expr.b);

        self.exprs[node].kind = ExprKind::Conjunction;
        self.exprs[node].a = a;
        self.exprs[node].b = self.expr_new(ExprKind::Tautology, 0, 0);

        true
    }

    pub fn inv_dis_identity(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        let a = self.expr_new(expr.kind, expr.a, expr.b);

        self.exprs[node].kind = ExprKind::Disjunction;
        self.exprs[node].a = a;
        self.exprs[node].b = self.expr_new(ExprKind::Contradiction, 0, 0);

        true
    }

    pub fn fwd_annihilation(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);

        let rhs = self.exprs[expr.b];
        ensure!(rhs.kind == match expr.kind {
            ExprKind::Conjunction => ExprKind::Contradiction,
            ExprKind::Disjunction => ExprKind::Tautology,
            _ => unreachable!(),
        });

        self.exprs[node].kind = rhs.kind;

        self.expr_delete(expr.a);
        self.expr_free(expr.b);

        true
    }

    // pub fn inv_annihilation(&mut self, node: ExprRef) -> bool {
    //     let expr = self.exprs[node];
    //     ensure!(expr.kind == ExprKind::Contradiction || expr.kind == ExprKind::Tautology);

    //     self.exprs[node].kind = match expr.kind {
    //         ExprKind::Contradiction => ExprKind::Conjunction,
    //         ExprKind::Tautology => ExprKind::Disjunction,
    //         _ => unreachable!(),
    //     };

    //     self.exprs[node].a = self.expr_new(ExprKind::Any, 0, 0);
    //     self.exprs[node].b = self.expr_new(expr.kind, 0, 0);

    //     true
    // }

    pub fn fwd_inverse(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Negation);

        let atomic = self.exprs[expr.a];
        ensure!(atomic.kind == ExprKind::Tautology || atomic.kind == ExprKind::Contradiction);

        self.exprs[node].kind = atomic.kind.get_dual();

        self.expr_free(expr.a);

        true
    }

    pub fn inv_inverse(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Tautology || expr.kind == ExprKind::Contradiction);

        self.exprs[node].kind = ExprKind::Negation;
        self.exprs[node].a = self.expr_new(expr.kind.get_dual(), 0, 0);

        true
    }

    pub fn fwd_absorption(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);
        ensure!(self.assert_binary(expr.b, expr.kind.get_dual()));

        let rhs = self.exprs[expr.b];
        let Some((a, b)) = self.order_eq_exprs(expr.a, rhs.a) else { return false };

        self.exprs[node] = self.exprs[a];

        self.expr_free(a);
        self.expr_delete(b);
        self.expr_delete(rhs.b);
        self.expr_free(expr.b);

        true
    }

    // pub fn inv_con_absorption(&mut self, node: ExprRef) -> bool {
    //     let expr = self.exprs[node];
    //     let a = self.expr_new(expr.kind, expr.a, expr.b);
    //     let copy = self.expr_copy(node);
    //     let any = self.expr_new(ExprKind::Any, 0, 0);
    //     let b = self.expr_new(ExprKind::Disjunction, copy, any);

    //     self.exprs[node].kind = ExprKind::Conjunction;
    //     self.exprs[node].a = a;
    //     self.exprs[node].b = b;

    //     true
    // }

    // pub fn inv_dis_absorption(&mut self, node: ExprRef) -> bool {
    //     let expr = self.exprs[node];
    //     let a = self.expr_new(expr.kind, expr.a, expr.b);
    //     let copy = self.expr_copy(node);
    //     let any = self.expr_new(ExprKind::Any, 0, 0);
    //     let b = self.expr_new(ExprKind::Conjunction, copy, any);

    //     self.exprs[node].kind = ExprKind::Disjunction;
    //     self.exprs[node].a = a;
    //     self.exprs[node].b = b;

    //     true
    // }

    pub fn fwd_reduction(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);
        ensure!(self.assert_binary(expr.b, expr.kind.get_dual()));

        let rhs = self.exprs[expr.b];
        ensure!(self.assert_negation(rhs.a));
        let negation = self.exprs[rhs.a];
        let Some((a, b)) = self.order_eq_exprs(expr.a, negation.a) else { return false };

        self.exprs[node].a = a;
        self.exprs[node].b = rhs.b;

        self.expr_delete(b);
        self.expr_free(rhs.a);
        self.expr_free(expr.b);

        true
    }

    pub fn inv_reduction(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);

        let copy = self.expr_copy(expr.a);
        let negation = self.expr_new(ExprKind::Negation, copy, 0);
        let binary = self.expr_new(expr.kind.get_dual(), negation, expr.b);

        self.exprs[node].b = binary;

        true
    }

    pub fn fwd_adjacency(&mut self, node: ExprRef) -> bool {
        let expr = self.exprs[node];
        ensure!(expr.kind == ExprKind::Conjunction || expr.kind == ExprKind::Disjunction);

        let dual = expr.kind.get_dual();
        ensure!(self.assert_binary(expr.a, dual) && self.assert_binary(expr.b, dual));

        let lhs = self.exprs[expr.a];
        let rhs = self.exprs[expr.b];
        ensure!(self.assert_negation(rhs.b));

        let negation = self.exprs[rhs.b];
        let Some((a, b)) = self.order_eq_exprs(lhs.a, rhs.a) else { return false };
        ensure!(self.expr_eq(lhs.b, negation.a));

        self.exprs[node] = self.exprs[a];

        self.expr_free(a);
        self.expr_free(expr.a);
        self.expr_free(expr.b);
        self.expr_delete(b);
        self.expr_delete(lhs.b);
        self.expr_delete(rhs.b);

        true
    }

    // pub fn inv_con_adjacency(&mut self, node: ExprRef) -> bool {
    //     let expr = self.exprs[node];
    //     let a = self.expr_new(expr.kind, expr.a, expr.b);
    //     let copy = self.expr_copy(node);
    //     let any_a = self.expr_new(ExprKind::Any, 0, 0);
    //     let any_b = self.expr_new(ExprKind::Any, 0, 0);
    //     let negation = self.expr_new(ExprKind::Negation, any_b, 0);
    //     let lhs = self.expr_new(ExprKind::Disjunction, a, any_a);
    //     let rhs = self.expr_new(ExprKind::Disjunction, copy, negation);

    //     self.exprs[node].kind = ExprKind::Conjunction;
    //     self.exprs[node].a = lhs;
    //     self.exprs[node].b = rhs;

    //     true
    // }

    // pub fn inv_dis_adjacency(&mut self, node: ExprRef) -> bool {
    //     let expr = self.exprs[node];
    //     let a = self.expr_new(expr.kind, expr.a, expr.b);
    //     let copy = self.expr_copy(node);
    //     let any_a = self.expr_new(ExprKind::Any, 0, 0);
    //     let any_b = self.expr_new(ExprKind::Any, 0, 0);
    //     let negation = self.expr_new(ExprKind::Negation, any_b, 0);
    //     let lhs = self.expr_new(ExprKind::Conjunction, a, any_a);
    //     let rhs = self.expr_new(ExprKind::Conjunction, copy, negation);

    //     self.exprs[node].kind = ExprKind::Disjunction;
    //     self.exprs[node].a = lhs;
    //     self.exprs[node].b = rhs;

    //     true
    // }
}
