//! Minimal parser for the TLA+ values TLC prints in simulation trace files.
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq)]
pub enum V {
    Int(i64),
    Str(String),
    Bool(bool),
    Model(String),           // model value, e.g. d1
    Set(Vec<V>),             // {a, b}
    Tuple(Vec<V>),           // <<a, b>>
    Rec(BTreeMap<String, V>), // [f |-> v, ...]
    Fun(Vec<(V, V)>),        // (a :> x @@ b :> y)
}

impl V {
    pub fn int(&self) -> i64 { match self { V::Int(i) => *i, _ => panic!("not int: {self:?}") } }
    pub fn str(&self) -> &str { match self { V::Str(s) => s, _ => panic!("not string: {self:?}") } }
    pub fn bool(&self) -> bool { match self { V::Bool(b) => *b, _ => panic!("not bool: {self:?}") } }
    pub fn model(&self) -> &str { match self { V::Model(s) => s, _ => panic!("not model value: {self:?}") } }
    pub fn set(&self) -> &[V] { match self { V::Set(s) => s, _ => panic!("not set: {self:?}") } }
    pub fn tuple(&self) -> &[V] { match self { V::Tuple(s) => s, _ => panic!("not tuple: {self:?}") } }
    pub fn field(&self, f: &str) -> &V {
        match self { V::Rec(r) => r.get(f).unwrap_or_else(|| panic!("no field {f}")), _ => panic!("not record") }
    }
    /// Apply a function value to an argument.
    pub fn app(&self, k: &V) -> &V {
        match self {
            V::Fun(m) => &m.iter().find(|(a, _)| a == k).unwrap_or_else(|| panic!("{k:?} not in domain")).1,
            _ => panic!("not a function: {self:?}"),
        }
    }
}

struct P<'a> { s: &'a [u8], i: usize }

impl<'a> P<'a> {
    fn ws(&mut self) { while self.i < self.s.len() && (self.s[self.i] as char).is_whitespace() { self.i += 1; } }
    fn eat(&mut self, t: &str) -> bool {
        self.ws();
        if self.s[self.i..].starts_with(t.as_bytes()) { self.i += t.len(); true } else { false }
    }
    fn expect(&mut self, t: &str) {
        if !self.eat(t) { panic!("expected {t:?} at {:?}", String::from_utf8_lossy(&self.s[self.i..(self.i + 30).min(self.s.len())])) }
    }
    fn ident(&mut self) -> String {
        self.ws();
        let st = self.i;
        while self.i < self.s.len() && ((self.s[self.i] as char).is_alphanumeric() || self.s[self.i] == b'_') { self.i += 1; }
        String::from_utf8(self.s[st..self.i].to_vec()).unwrap()
    }
    fn list(&mut self, close: &str) -> Vec<V> {
        let mut v = vec![];
        if self.eat(close) { return v; }
        loop {
            v.push(self.val());
            if self.eat(close) { return v; }
            self.expect(",");
        }
    }
    fn val(&mut self) -> V {
        self.ws();
        if self.eat("<<") { return V::Tuple(self.list(">>")); }
        if self.eat("{") { return V::Set(self.list("}")); }
        if self.eat("[") {
            let mut r = BTreeMap::new();
            loop {
                let k = self.ident();
                self.expect("|->");
                r.insert(k, self.val());
                if self.eat("]") { return V::Rec(r); }
                self.expect(",");
            }
        }
        if self.eat("(") {
            let mut m = vec![];
            loop {
                let k = self.val();
                self.expect(":>");
                let x = self.val();
                m.push((k, x));
                if self.eat(")") { return V::Fun(m); }
                self.expect("@@");
            }
        }
        if self.eat("\"") {
            let st = self.i;
            while self.s[self.i] != b'"' { self.i += 1; }
            let r = String::from_utf8(self.s[st..self.i].to_vec()).unwrap();
            self.i += 1;
            return V::Str(r);
        }
        let neg = self.eat("-");
        self.ws();
        if (self.s[self.i] as char).is_ascii_digit() {
            let id = self.ident();
            let n: i64 = id.parse().unwrap();
            return V::Int(if neg { -n } else { n });
        }
        let id = self.ident();
        match id.as_str() {
            "TRUE" => V::Bool(true),
            "FALSE" => V::Bool(false),
            "" => panic!("cannot parse value at {}", self.i),
            _ => V::Model(id),
        }
    }
}

pub type State = BTreeMap<String, V>;

/// Parses a TLC `-simulate file=...` trace module into its sequence of states.
pub fn parse_trace(text: &str) -> Vec<State> {
    let mut states = vec![];
    for chunk in text.split("STATE_").skip(1) {
        let body = &chunk[chunk.find("==").expect("STATE_n ==") + 2..];
        let mut st = State::new();
        for conj in body.split("\n/\\ ").map(|c| c.trim().trim_start_matches("/\\").trim()) {
            if conj.is_empty() || conj.starts_with("====") { continue; }
            let conj = conj.split("\n====").next().unwrap();
            let eq = conj.find(" = ").expect("var = value");
            let name = conj[..eq].trim().to_string();
            let mut p = P { s: conj[eq + 3..].as_bytes(), i: 0 };
            st.insert(name, p.val());
        }
        states.push(st);
    }
    states
}

/// Parses `NAME = value` constants from a TLC .cfg file.
pub fn parse_cfg(text: &str) -> BTreeMap<String, V> {
    let mut m = BTreeMap::new();
    for line in text.lines() {
        let l = line.trim();
        if let Some(eq) = l.find(" = ") {
            let mut p = P { s: l[eq + 3..].as_bytes(), i: 0 };
            m.insert(l[..eq].trim().to_string(), p.val());
        }
    }
    m
}
