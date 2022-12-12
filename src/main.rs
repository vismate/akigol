#![feature(let_chains, iter_intersperse, iterator_try_collect)]
use smallmap::{Map, Set};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Interpretation(Map<PVar, bool>);

#[derive(Debug)]
struct ConditionSet(Set<Interpretation>);

impl Interpretation {
    fn new(elems: impl IntoIterator<Item = (PVar, bool)>) -> Self {
        Self(elems.into_iter().collect())
    }
}

impl std::ops::BitAnd for Interpretation {
    type Output = Option<Self>;
    fn bitand(mut self, rhs: Self) -> <Self as std::ops::BitAnd>::Output {
        for (k, v) in rhs.0 {
            match self.0.get(&k) {
                Some(&b) => {
                    if v != b {
                        return None;
                    };
                    continue;
                }
                _ => {
                    self.0.insert(k, v);
                }
            }
        }

        Some(self)
    }
}

impl std::fmt::Display for Interpretation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for (k, v) in self.0.iter() {
            write!(f, "\'{k}\': {v} ")?;
        }

        Ok(())
    }
}

impl std::fmt::Display for ConditionSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for (k, _) in self.0.iter() {
            writeln!(f, "{k}")?;
        }

        Ok(())
    }
}

impl ConditionSet {
    fn new(elems: impl IntoIterator<Item = Interpretation>) -> Self {
        Self(elems.into_iter().zip((0..).map(|_| {})).collect())
    }

    fn to_table(&self, base: &Base) -> String {
        let mut table: String = base.iter().map(|var| var.0).intersperse(' ').collect();
        table.push('\n');
        table.push_str("-".repeat(table.len()).as_str());
        table.push('\n');
        for interpretation in self.0.keys() {
            let mut row = String::new();
            for var in base {
                row.push(if let Some(b) = interpretation.0.get(var) {
                    if *b {
                        'T'
                    } else {
                        'F'
                    }
                } else {
                    '*'
                });
                row.push(' ');
            }
            row.push('\n');
            table.push_str(row.as_str());
        }

        table
    }
}

impl std::ops::BitAnd for ConditionSet {
    type Output = Self;
    fn bitand(self, rhs: Self) -> <Self as std::ops::BitAnd>::Output {
        let mut set = Set::new();
        for k1 in self.0.keys() {
            for k2 in rhs.0.keys() {
                if let Some(e) = k1.clone() & k2.clone() {
                    set.insert(e, ());
                }
            }
        }

        Self(set)
    }
}

impl std::ops::BitOr for ConditionSet {
    type Output = Self;
    fn bitor(mut self, rhs: Self) -> <Self as std::ops::BitOr>::Output {
        for k in rhs.0.keys() {
            self.0.insert(k.clone(), ());
        }

        self
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
struct PVar(char);

impl PVar {
    fn is_pvar(c: char) -> bool {
        matches!(c, 'A'..='Z')
    }

    fn from_char(c: char) -> Option<Self> {
        if Self::is_pvar(c) {
            Some(Self(c))
        } else {
            None
        }
    }
}

impl std::fmt::Display for PVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

type Base = Vec<PVar>;

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
enum BinOpType {
    Conjunction,
    Disjunction,
    Implication,
}

impl BinOpType {
    fn priority(self) -> u8 {
        match self {
            Self::Conjunction => 30,
            Self::Disjunction => 20,
            Self::Implication => 10,
        }
    }

    fn is_right_associative(self) -> bool {
        matches!(self, Self::Implication)
    }

    fn from_char(c: char) -> Option<Self> {
        match c {
            '&' => Some(Self::Conjunction),
            '|' => Some(Self::Disjunction),
            '>' => Some(Self::Implication),
            _ => None,
        }
    }
}

#[allow(clippy::enum_variant_names)]
#[derive(Debug)]
enum ASTNode {
    PVarNode(PVar),
    NegationNode(Box<ASTNode>),
    BinOpNode {
        op: BinOpType,
        left: Box<ASTNode>,
        right: Box<ASTNode>,
    },
}

impl ASTNode {
    fn complexity(&self) -> u32 {
        match self {
            Self::PVarNode(_) => 0,
            Self::NegationNode(v) => v.complexity() + 1,
            Self::BinOpNode { op: _, left, right } => left.complexity() + right.complexity() + 1,
        }
    }

    fn eval(&self, interpretation: &Interpretation) -> bool {
        match self {
            Self::PVarNode(v) => {
                *(interpretation
                    .0
                    .get(v)
                    .expect("interpretaion should contain every variable"))
            }
            Self::NegationNode(v) => !v.eval(interpretation),
            Self::BinOpNode {
                op: BinOpType::Conjunction,
                left,
                right,
            } => left.eval(interpretation) && right.eval(interpretation),
            Self::BinOpNode {
                op: BinOpType::Disjunction,
                left,
                right,
            } => left.eval(interpretation) || right.eval(interpretation),
            Self::BinOpNode {
                op: BinOpType::Implication,
                left,
                right,
            } => !left.eval(interpretation) || right.eval(interpretation),
        }
    }

    fn require(&self, b: bool) -> ConditionSet {
        match self {
            Self::PVarNode(v) => ConditionSet::new([Interpretation::new([(*v, b)])]),
            Self::NegationNode(ref v) => v.require(!b),
            Self::BinOpNode {
                op: BinOpType::Conjunction,
                left,
                right,
            } => {
                let left = left.require(b);
                let right = right.require(b);

                if b {
                    left & right
                } else {
                    left | right
                }
            }
            Self::BinOpNode {
                op: BinOpType::Disjunction,
                left,
                right,
            } => {
                let left = left.require(b);
                let right = right.require(b);

                if b {
                    left | right
                } else {
                    left & right
                }
            }
            Self::BinOpNode {
                op: BinOpType::Implication,
                left,
                right,
            } => {
                if b {
                    left.require(false) | right.require(true)
                } else {
                    left.require(true) & right.require(false)
                }
            }
        }
    }
}

impl std::fmt::Display for ASTNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PVarNode(v) => write!(f, "{v}"),
            Self::NegationNode(e) => write!(f, "!{e}"),
            Self::BinOpNode { op, left, right } => write!(
                f,
                "({left} {} {right})",
                match op {
                    BinOpType::Conjunction => '&',
                    BinOpType::Disjunction => '|',
                    BinOpType::Implication => '>',
                }
            ),
        }
    }
}

fn check_parens(tokens: &[Token]) -> Result<(), String> {
    let mut opens = vec![];
    for tok in tokens.iter() {
        match tok {
            Token::OpenParen(_, _) => {
                opens.push(tok);
            }
            Token::CloseParen(i, close_paren_type) => {
                match opens.pop() {
                    None => {
                        return Err(format!(
                            "@{} -> unmatched \'{close_paren_type:?}\' closing paren",
                            i + 1
                        ));
                    }

                    Some(Token::OpenParen(j, open_paren_type)) if close_paren_type != open_paren_type => return Err(format!("@{} -> mismatched paren types: \'{open_paren_type:?}\':@{} and \'{close_paren_type:?}\':@{}", i + 1, j + 1, i + 1)),
                _ => {}
                }
            }
            _ => {}
        }
    }

    if let Some(Token::OpenParen(i, paren_type)) = opens.pop() {
        Err(format!(
            "@{} -> unmatched \'{paren_type:?}\' open paren",
            i + 1
        ))
    } else {
        Ok(())
    }
}

fn check_neighbour_correctness(tokens: &[Token]) -> Result<(), String> {
    let mut iter = tokens.iter();
    let mut current: Option<&Token> = None;
    let mut next = iter.next();

    while current.is_some() || next.is_some() {
        match (current, next) {
            (None, Some(Token::BinOp(i, op))) => Err(format!(
                "@{} -> expression cannot start with binary operator: \'{op:?}\'", i+1
            )),
            (Some(Token::Variable(i, v1)), Some(Token::Variable(j, v2))) => Err(format!(
                "@{} -> variable \'{v1}\':@{} cannot be followed by an other variable: \'{v2}\':@{}", i + 1, i+1, j+1
            )),
            (Some(Token::Variable(i, v)), Some(Token::Negation(j))) => {
                Err(format!("@{} -> variable \'{v}\':@{} cannot be followed by unary operator: \'!\':@{}", i+1, i+1, j+1 ))
            }
            (Some(Token::Variable(i, v)), Some(Token::OpenParen(j, t))) => {
                Err(format!("@{} -> variable \'{v}\':@{} cannot be followed by \'{t:?}\' open paren:@{}", i+1, i+1, j+1))
            }
            (Some(Token::BinOp(i, op)), None) => Err(format!(
                "@{} -> binary operator \'{op:?}\' must be followed by an expression", i+1)
            ),
            (Some(Token::BinOp(i, op1)), Some(Token::BinOp(j, op2)))  => Err(format!(
                "@{} -> binary operator \'{op1:?}\':@{} cannot be followed by another binary operator: \'{op2:?}\':@{}", i+1, i+1, j+1
            )),
            (Some(Token::BinOp(i, op)), Some(Token::CloseParen(j, t))) => {
                Err(format!("@{} -> binary operator \'{op:?}\':@{} cannot be followed by a \'{t:?}\' closed paren:@{}", i+1, i+1, j+1))
            }
            (Some(Token::Negation(i)), None) => {
                Err(format!("@{} -> unary operator \'!\' must be followed by an expression", i+1))
            }
            (Some(Token::Negation(i)), Some(Token::BinOp(j, op))) => Err(format!(
                "@{} -> unary operator \'!\':@{} cannot be followed by binary operator: \'{op:?}\':@{}", i+1, i+1, j+1
            )),
            (Some(Token::Negation(i)), Some(Token::CloseParen(j, t))) => {
                Err(format!("@{} -> unary operator \'!\':@{} cannot be followed by \'{t:?}\' closed paren:@{}", i+1, i+1, j+1))
            }
            (Some(Token::OpenParen(i, t)), Some(Token::BinOp(j, op))) => Err(format!(
                "@{} -> \'{t:?}\' open paren:@{} cannot be followed by binary operator: \'{op:?}\':@{}", i+1, i+1, j+1 
            )),
            (Some(Token::OpenParen(i, t1)), Some(Token::CloseParen(j, t2))) if t1 == t2 => Err(format!("@{} -> \'{t1:?}\' open paren:@{} cannot be immidiately closed by \'{t2:?}\' closed paren:@{}", i+1, i+1, j+1)),
            (Some(Token::CloseParen(i, t)), Some(Token::Variable(j, v))) => Err(format!(
                "@{} -> \'{t:?}\' closed paren:@{} cannot be followed by variable: \'{v}\':@{}", i+1, i+1, j+1
            )),
            (Some(Token::CloseParen(i, t)), Some(Token::Negation(j))) => {
                Err(format!("@{} -> \'{t:?}\' closed paren:@{} cannot be followed by unary operator: \'!\':@{}", i+1, i+1, j+1))
            }
            (Some(Token::CloseParen(i, t1)), Some(Token::OpenParen(j, t2))) => {
                Err(format!("@{} -> \'{t1:?}\' closed paren:@{} cannot be followed by \'{t2:?}\' open paren:@{}", i+1, i+1, j+1))
            }
            _ => Ok(()),
        }?;

        current = next;
        next = iter.next();
    }

    Ok(())
}

fn validate(tokens: &[Token]) -> Result<(), String> {
    check_parens(tokens)?;
    check_neighbour_correctness(tokens)
}

fn parse(expr: &str) -> Result<Expression, String> {
    let tokens = tokenize(expr).try_collect::<Vec<_>>()?;

    validate(&tokens)?;

    let mut operator_stack = vec![];
    let mut operand_stack = vec![];
    let mut base = Set::new();

    let apply_op = |op: Token, stack: &mut Vec<ASTNode>| match op {
        Token::Negation(_) => {
            let v = stack
                .pop()
                .expect("should have 1 operand available in stack");
            stack.push(ASTNode::NegationNode(Box::new(v)));
        }
        Token::BinOp(_, op) => {
            let right = stack
                .pop()
                .expect("should have 2 operands available in stack");
            let left = stack
                .pop()
                .expect("should have 1 operand available in stack");
            stack.push(ASTNode::BinOpNode {
                op,
                left: Box::new(left),
                right: Box::new(right),
            });
        }
        tok => unreachable!("not operator: {tok:?}"),
    };

    'main: for tok in tokens {
        match tok {
            Token::OpenParen(_, _) | Token::Negation(_) => {
                operator_stack.push(tok);
            }
            Token::CloseParen(_, _) => {
                while !operator_stack.is_empty() {
                    let popped = operator_stack.pop().expect("op stack should not be empty");

                    match popped {
                        Token::OpenParen(_, _) => {
                            continue 'main;
                        }
                        op => apply_op(op, &mut operand_stack),
                    }
                }
                unreachable!("Unbalanced right parentheses")
            }
            Token::BinOp(_, op1) => {
                let higher_priority = |tok: Token| match tok {
                    Token::BinOp(_, op2) => {
                        (!op1.is_right_associative() && op1.priority() == op2.priority())
                            || op1.priority() < op2.priority()
                    }
                    Token::Negation(_) => true,
                    _ => false,
                };

                while let Some(op2) = operator_stack.last() {
                    if higher_priority(*op2) {
                        apply_op(operator_stack.pop().unwrap(), &mut operand_stack);
                    } else {
                        break;
                    }
                }

                operator_stack.push(tok);
            }
            Token::Variable(_, v) => {
                let v = PVar::from_char(v).unwrap();
                operand_stack.push(ASTNode::PVarNode(v));
                base.insert(v, ());
            }
        }
    }

    for op in operator_stack.into_iter().rev() {
        apply_op(op, &mut operand_stack);
    }

    let ast = operand_stack
        .pop()
        .ok_or_else(|| "parsing failed: no operand left on stack".to_string())?;

    Ok(Expression {
        ast,
        base: base.keys().copied().collect(),
    })
}

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
enum ParenType {
    Normal,
    Square,
    Curly,
}

impl ParenType {
    fn from_char(c: char) -> Option<Self> {
        match c {
            '(' | ')' => Some(Self::Normal),
            '[' | ']' => Some(Self::Square),
            '{' | '}' => Some(Self::Curly),
            _ => None,
        }
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
enum Token {
    Negation(usize),
    Variable(usize, char),
    BinOp(usize, BinOpType),
    OpenParen(usize, ParenType),
    CloseParen(usize, ParenType),
}

impl Token {
    fn is_variable(c: char) -> bool {
        matches!(c, 'A'..='Z')
    }

    fn is_binop(c: char) -> bool {
        matches!(c, '&' | '|' | '>')
    }

    fn is_open_paren(c: char) -> bool {
        matches!(c, '(' | '[' | '{')
    }

    fn is_close_paren(c: char) -> bool {
        matches!(c, ')' | ']' | '}')
    }
}

fn tokenize(expr: &str) -> impl Iterator<Item = Result<Token, String>> + '_ {
    expr.chars().enumerate().filter_map(|(i, c)| match c {
        '!' => Some(Ok(Token::Negation(i))),
        c if Token::is_variable(c) => Some(Ok(Token::Variable(i, c))),
        c if Token::is_binop(c) => Some(Ok(Token::BinOp(i, BinOpType::from_char(c).unwrap()))),
        c if Token::is_open_paren(c) => {
            Some(Ok(Token::OpenParen(i, ParenType::from_char(c).unwrap())))
        }
        c if Token::is_close_paren(c) => {
            Some(Ok(Token::CloseParen(i, ParenType::from_char(c).unwrap())))
        }
        c if c.is_whitespace() => None,
        _ => Some(Err(format!("@{} -> invalid character: \'{c}\'", i + 1))),
    })
}

struct Expression {
    ast: ASTNode,
    base: Base,
}

impl Expression {
    fn require(&self, b: bool) -> ConditionSet {
        self.ast.require(b)
    }

    fn requirements_table(&self, b: bool) -> String {
        self.require(b).to_table(&self.base)
    }

    fn complexity(&self) -> u32 {
        self.ast.complexity()
    }

    fn eval(&self, interpretation: &Interpretation) -> bool {
        self.ast.eval(interpretation)
    }
}

fn main() {
    if let Some(expr) = std::env::args().nth(1) {
        match parse(expr.as_str()) {
            Ok(expr) => {
                println!("Expression: {}", expr.ast);
                println!("Complexity = {}\n", expr.complexity());
                println!("True if:");
                println!("{}", expr.requirements_table(true));
                let interpretation = Interpretation::new(
                    expr.base
                        .iter()
                        .copied()
                        .zip([false, true, true].into_iter().cycle()),
                );
                println!("False if:");
                println!("{}", expr.requirements_table(false));
                println!("If {interpretation} -->  {}", expr.eval(&interpretation));
            }
            Err(msg) => {
                eprintln!("{msg}");
            }
        }
    } else {
        eprintln!("Please provide an expression");
    }
}
