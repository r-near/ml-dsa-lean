//! Static worst-case stack depth from compiler output.
//!
//! Modes
//!   walker elf  --arch x86|thumb|riscv --sizes FILE --dis FILE [--exclude A,B] [--min-frame N]
//!       FILE for --sizes is `llvm-readobj --stack-sizes` output, FILE for --dis is
//!       `llvm-objdump -d --no-show-raw-insn -l` output (-l is optional) of the same linked ELF.
//!   walker wasm --dis FILE [--exclude A,B] [--min-frame N]
//!       `llvm-objdump -d --no-show-raw-insn` of a wasm module; frames come from the shadow-stack prologue.
//!   walker allocas --ll FILE [--min N]
//!       per function allocas of at least N bytes in optimized LLVM IR (`--emit=llvm-ir -Zfewer-names=no`).
//!
//! The call graph has an edge for every direct call and every direct jump to the start of another function
//! (a tail call replaces the frame, counting it as a call is an over-estimate). Indirect calls, functions with
//! no recorded frame size and recursion are reported, never silently counted as zero.
use rustc_demangle::demangle;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;

#[derive(Default)]
struct Func {
    name: String,
    frame: Option<u64>,
    callees: Vec<usize>,
    indirect: usize,
}

struct Graph {
    funcs: Vec<Func>,
    by_name: HashMap<String, usize>,
    /// bytes pushed by the call instruction itself (x86 return address)
    call_overhead: u64,
}

fn dem(s: &str) -> String {
    // `{:#}` drops the hash suffix.
    format!("{:#}", demangle(s))
}

fn arg(args: &[String], key: &str) -> Option<String> {
    args.iter().position(|a| a == key).and_then(|i| args.get(i + 1)).cloned()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mode = args.first().map(String::as_str).unwrap_or("");
    let min_frame: u64 = arg(&args, "--min-frame").and_then(|s| s.parse().ok()).unwrap_or(1024);
    let exclude: Vec<String> = arg(&args, "--exclude")
        .map(|s| s.split(',').filter(|x| !x.is_empty()).map(String::from).collect())
        .unwrap_or_default();
    match mode {
        "elf" => {
            let arch = arg(&args, "--arch").expect("--arch");
            let sizes = fs::read_to_string(arg(&args, "--sizes").expect("--sizes")).unwrap();
            let dis = fs::read_to_string(arg(&args, "--dis").expect("--dis")).unwrap();
            let g = parse_elf(&arch, &sizes, &dis);
            report(&g, &exclude, min_frame);
        }
        "wasm" => {
            let dis = fs::read_to_string(arg(&args, "--dis").expect("--dis")).unwrap();
            let g = parse_wasm(&dis);
            report(&g, &exclude, min_frame);
        }
        "allocas" => {
            let ll = fs::read_to_string(arg(&args, "--ll").expect("--ll")).unwrap();
            let min: u64 = arg(&args, "--min").and_then(|s| s.parse().ok()).unwrap_or(1024);
            allocas(&ll, min);
        }
        _ => {
            eprintln!("usage: walker elf|wasm|allocas ... (see source header)");
            std::process::exit(2);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// ELF (x86_64, thumbv7em, riscv32)
// ---------------------------------------------------------------------------------------------

fn parse_sizes(text: &str) -> HashMap<String, u64> {
    let mut m = HashMap::new();
    let mut funcs: Vec<String> = Vec::new();
    for line in text.lines() {
        let l = line.trim();
        if let Some(rest) = l.strip_prefix("Functions: [") {
            funcs = rest.trim_end_matches(']').split(',').map(|s| s.trim().to_string()).collect();
        } else if let Some(rest) = l.strip_prefix("Size: 0x") {
            let n = u64::from_str_radix(rest.trim(), 16).unwrap();
            for f in funcs.drain(..) {
                m.insert(f, n);
            }
        }
    }
    m
}

/// Splits a disassembly line "  addr: mnemonic operands" into (mnemonic, operands).
fn split_insn(line: &str) -> Option<(&str, &str)> {
    let (addr, rest) = line.trim_start().split_once(':')?;
    if addr.is_empty() || !addr.chars().all(|c| c.is_ascii_hexdigit()) {
        return None;
    }
    let rest = rest.trim();
    if rest.is_empty() {
        return None;
    }
    match rest.split_once(char::is_whitespace) {
        Some((m, o)) => Some((m, o.trim())),
        None => Some((rest, "")),
    }
}

/// The `<label>` in an operand string, if any, as (symbol, has_offset).
fn label(ops: &str) -> Option<(&str, bool)> {
    let s = ops.rfind('<')?;
    let e = ops[s..].find('>')? + s;
    let inner = &ops[s + 1..e];
    match inner.rfind('+') {
        Some(p) if inner[p + 1..].starts_with("0x") => Some((&inner[..p], true)),
        _ => Some((inner, false)),
    }
}

fn parse_elf(arch: &str, sizes_text: &str, dis: &str) -> Graph {
    let sizes = parse_sizes(sizes_text);
    let mut funcs: Vec<Func> = Vec::new();
    let mut by_name: HashMap<String, usize> = HashMap::new();
    // pass 1: function headers
    for line in dis.lines() {
        if let Some(h) = line.strip_suffix(">:") {
            if let Some((addr, name)) = h.split_once(" <") {
                if addr.chars().all(|c| c.is_ascii_hexdigit()) && !addr.is_empty() && !name.starts_with('$') {
                    by_name.entry(name.to_string()).or_insert_with(|| {
                        funcs.push(Func { name: name.to_string(), frame: sizes.get(name).copied(), ..Default::default() });
                        funcs.len() - 1
                    });
                }
            }
        }
    }
    // pass 2: edges
    let mut cur: Option<usize> = None;
    for line in dis.lines() {
        if let Some(h) = line.strip_suffix(">:") {
            if let Some((addr, name)) = h.split_once(" <") {
                if addr.chars().all(|c| c.is_ascii_hexdigit()) && !addr.is_empty() {
                    cur = by_name.get(name).copied();
                    continue;
                }
            }
        }
        let Some(c) = cur else { continue };
        let Some((m, ops)) = split_insn(line) else { continue };
        let transfers = match arch {
            "x86" => m.starts_with("call") || m.starts_with("jmp") || (m.starts_with('j') && !m.starts_with("jmp")),
            "thumb" => m.starts_with("bl") || m == "b" || m.starts_with("b.") || m.starts_with("cb") || {
                // conditional branches: beq, bne, bhi.w ...
                m.len() >= 3 && m.starts_with('b') && !m.starts_with("bic") && !m.starts_with("bfi") && !m.starts_with("bfc") && !m.starts_with("bkpt") && !m.starts_with("bx")
            },
            "riscv" => matches!(m, "jal" | "j" | "call" | "tail") || m.starts_with('b') || m == "jalr" || m == "jr",
            _ => panic!("arch"),
        };
        if !transfers {
            continue;
        }
        // indirect transfers
        let indirect = match arch {
            "x86" => (m.starts_with("call") || m.starts_with("jmp")) && ops.contains('*') && label(ops).is_none(),
            "thumb" => (m == "blx" || m == "bx") && !ops.contains("lr") && label(ops).is_none() && m == "blx",
            "riscv" => m == "jalr" && !ops.starts_with("zero, 0(ra)") && label(ops).is_none() && !ops.contains("(ra)") || m == "jalr" && ops.starts_with("ra,"),
            _ => false,
        };
        if indirect && (m.starts_with("call") || m == "blx" || m == "jalr") {
            funcs[c].indirect += 1;
        }
        if let Some((target, off)) = label(ops) {
            if off || target.starts_with('$') {
                continue;
            }
            if let Some(&t) = by_name.get(target) {
                if t != c && !funcs[c].callees.contains(&t) {
                    funcs[c].callees.push(t);
                } else if t == c && (m.starts_with("call") || m.starts_with("bl") || m == "jal") {
                    funcs[c].indirect += 1000; // direct self-recursion marker
                }
            }
        }
    }
    Graph { funcs, by_name, call_overhead: if arch == "x86" { 8 } else { 0 } }
}

// ---------------------------------------------------------------------------------------------
// wasm
// ---------------------------------------------------------------------------------------------

fn parse_wasm(dis: &str) -> Graph {
    // Function indices follow the order of the function bodies in the module (this module imports nothing;
    // the check below fails loudly if a call index is out of range).
    let mut funcs: Vec<Func> = Vec::new();
    let mut by_name: HashMap<String, usize> = HashMap::new();
    let mut cur: Option<usize> = None;
    let mut window: Vec<(String, String)> = Vec::new();
    let mut calls: Vec<(usize, usize)> = Vec::new();
    for line in dis.lines() {
        if let Some(h) = line.strip_suffix(">:") {
            if let Some((_, name)) = h.split_once(" <") {
                if name == "CODE" {
                    continue; // the section header, not a function
                }
                funcs.push(Func { name: name.to_string(), frame: Some(0), ..Default::default() });
                let i = funcs.len() - 1;
                by_name.entry(name.to_string()).or_insert(i);
                cur = Some(i);
                window.clear();
                continue;
            }
        }
        let Some(c) = cur else { continue };
        let Some((m, ops)) = split_insn(line) else { continue };
        if window.len() < 12 {
            window.push((m.to_string(), ops.to_string()));
            // shadow stack prologue: global.get G; i32.const N; i32.sub
            let n = window.len();
            if n >= 3 && window[n - 1].0 == "i32.sub" && window[n - 2].0 == "i32.const" && window[n - 3].0 == "global.get" {
                if let Ok(v) = window[n - 2].1.trim().parse::<i64>() {
                    funcs[c].frame = Some(v.max(0) as u64);
                }
            }
        }
        if m == "call" {
            let idx: usize = ops.split_whitespace().next().and_then(|x| x.parse().ok()).expect("call index");
            calls.push((c, idx));
        } else if m == "call_indirect" || m == "return_call_indirect" {
            funcs[c].indirect += 1;
        }
    }
    for (c, idx) in calls {
        assert!(idx < funcs.len(), "call index {idx} out of range: the module has imports or the index space is not the body order");
        if idx == c {
            funcs[c].indirect += 1000;
        } else if !funcs[c].callees.contains(&idx) {
            funcs[c].callees.push(idx);
        }
    }
    Graph { funcs, by_name, call_overhead: 0 }
}

// ---------------------------------------------------------------------------------------------
// Analysis
// ---------------------------------------------------------------------------------------------

struct Walk<'a> {
    g: &'a Graph,
    skip: Vec<bool>,
    memo: HashMap<usize, (u64, Option<usize>)>,
    stack: HashSet<usize>,
    cycles: HashSet<usize>,
}

impl Walk<'_> {
    fn frame(&self, f: usize) -> u64 {
        self.g.funcs[f].frame.unwrap_or(0) + self.g.call_overhead
    }
    fn depth(&mut self, f: usize) -> u64 {
        if let Some(&(d, _)) = self.memo.get(&f) {
            return d;
        }
        if !self.stack.insert(f) {
            self.cycles.insert(f);
            return 0;
        }
        let mut best = (0u64, None);
        let callees = self.g.funcs[f].callees.clone();
        for c in callees {
            if self.skip[c] {
                continue;
            }
            let d = self.depth(c);
            if d > best.0 || best.1.is_none() {
                best = (d, Some(c));
            }
        }
        self.stack.remove(&f);
        let total = self.frame(f) + best.0;
        self.memo.insert(f, (total, best.1));
        total
    }
    fn chain(&self, mut f: usize) -> Vec<usize> {
        let mut v = vec![f];
        while let Some(&(_, Some(n))) = self.memo.get(&f) {
            v.push(n);
            f = n;
        }
        v
    }
}

fn report(g: &Graph, exclude: &[String], min_frame: u64) {
    let names: Vec<String> = g.funcs.iter().map(|f| dem(&f.name)).collect();
    let skip_panics: Vec<bool> = names.iter().map(|n| exclude.iter().any(|e| n.contains(e.as_str()))).collect();
    let none = vec![false; g.funcs.len()];
    let mut roots: Vec<usize> = (0..g.funcs.len()).filter(|&i| names[i].starts_with("ml_dsa_lean::api::")).collect();
    // When LTO inlined an api function into its exported wrapper (`stk_<name>`), root at the wrapper instead.
    let present: HashSet<String> = roots.iter().map(|&i| names[i].rsplit("::").next().unwrap().to_string()).collect();
    for i in 0..g.funcs.len() {
        if let Some(n) = names[i].strip_prefix("stk_") {
            if !present.contains(n) && !n.contains("::") {
                roots.push(i);
            }
        }
    }
    roots.sort_by_key(|&i| names[i].clone());
    let mut w_all = Walk { g, skip: none, memo: HashMap::new(), stack: HashSet::new(), cycles: HashSet::new() };
    let mut w_np = Walk { g, skip: skip_panics.clone(), memo: HashMap::new(), stack: HashSet::new(), cycles: HashSet::new() };
    println!("| root | worst case (bytes) | without panic paths (bytes) | own frame | chain (frame sizes, outermost first) |");
    println!("|---|---|---|---|---|");
    let mut reach: HashSet<usize> = HashSet::new();
    for &r in &roots {
        let a = w_all.depth(r);
        let b = w_np.depth(r);
        let chain = w_np.chain(r);
        let c: Vec<String> = chain
            .iter()
            .take(8)
            .map(|&i| format!("{} {}", short(&names[i]), g.funcs[i].frame.map(|x| x.to_string()).unwrap_or("?".into())))
            .collect();
        println!(
            "| {} | {} | {} | {} | {} |",
            names[r].trim_start_matches("ml_dsa_lean::api::").replace("stk_", "wrapper:"),
            a,
            b,
            w_all.frame(r),
            c.join(" > ")
        );
        let mut st = vec![r];
        while let Some(x) = st.pop() {
            if reach.insert(x) {
                st.extend(g.funcs[x].callees.iter().copied());
            }
        }
    }
    println!();
    println!("Frames of at least {min_frame} bytes among functions reachable from the api roots:");
    println!();
    println!("| function | frame (bytes) |");
    println!("|---|---|");
    let mut big: Vec<(u64, usize)> =
        reach.iter().filter_map(|&i| g.funcs[i].frame.filter(|&f| f >= min_frame).map(|f| (f, i))).collect();
    big.sort_by(|a, b| b.cmp(a));
    for (f, i) in big {
        println!("| {} | {} |", names[i], f);
    }
    println!();
    let nosize: Vec<&String> = reach.iter().filter(|&&i| g.funcs[i].frame.is_none()).map(|&i| &names[i]).collect();
    let mut nosize: Vec<&&String> = nosize.iter().collect();
    nosize.sort();
    println!("Reachable functions with no recorded frame size (counted as 0 plus call overhead): {}", nosize.len());
    for n in nosize.iter().take(30) {
        println!("  {n}");
    }
    let mut ind: Vec<&String> = reach.iter().filter(|&&i| g.funcs[i].indirect % 1000 > 0).map(|&i| &names[i]).collect();
    ind.sort();
    println!("Reachable functions containing indirect calls: {}", ind.len());
    for n in ind.iter().take(5) {
        println!("  {n}");
    }
    if ind.len() > 5 {
        println!("  ... ({} more)", ind.len() - 5);
    }
    let rec: Vec<&String> = reach.iter().filter(|&&i| g.funcs[i].indirect >= 1000).map(|&i| &names[i]).collect();
    println!("Reachable functions that call themselves directly: {}", rec.len());
    for n in rec {
        println!("  {n}");
    }
    let cyc: Vec<&String> = w_all.cycles.iter().chain(w_np.cycles.iter()).map(|&i| &names[i]).collect();
    println!("Call-graph cycles found: {}", cyc.len());
    for n in cyc {
        println!("  {n}");
    }
    println!("Functions reachable from the api roots: {}", reach.len());
    let _ = &g.by_name;
}

fn short(n: &str) -> String {
    let n = n.trim_start_matches("ml_dsa_lean::");
    let n = if let Some(p) = n.find('<') { format!("{}{}", &n[..p], "<..>") } else { n.to_string() };
    n
}

// ---------------------------------------------------------------------------------------------
// LLVM IR allocas
// ---------------------------------------------------------------------------------------------

fn alloca_size(ty: &str) -> Option<u64> {
    let ty = ty.trim();
    if let Some(rest) = ty.strip_prefix('[') {
        let (n, rest) = rest.split_once(" x ")?;
        let inner = rest.trim_end_matches(']');
        return Some(n.trim().parse::<u64>().ok()? * alloca_size(inner)?);
    }
    match ty {
        "i1" | "i8" => Some(1),
        "i16" => Some(2),
        "i32" | "float" | "ptr" => Some(4), // ptr is 8 on 64-bit targets; only large arrays matter here
        "i64" | "double" => Some(8),
        "i128" => Some(16),
        _ => None,
    }
}

fn allocas(ll: &str, min: u64) {
    let mut cur = String::new();
    let mut per: BTreeMap<String, Vec<(u64, String)>> = BTreeMap::new();
    for line in ll.lines() {
        if line.starts_with("define ") {
            if let Some(a) = line.find('@') {
                let rest = &line[a + 1..];
                let name = rest.split('(').next().unwrap_or("").trim_matches('"');
                cur = dem(name);
            }
        } else if let Some(p) = line.find(" = alloca ") {
            let var = line[..p].trim().to_string();
            let ty = line[p + 10..].split(',').next().unwrap_or("");
            if let Some(sz) = alloca_size(ty) {
                if sz >= min {
                    per.entry(cur.clone()).or_default().push((sz, var));
                }
            }
        }
    }
    println!("| function | alloca (bytes) | name |");
    println!("|---|---|---|");
    for (f, v) in per {
        let mut v = v;
        v.sort_by(|a, b| b.cmp(a));
        for (sz, var) in v {
            println!("| {f} | {sz} | {var} |");
        }
    }
}
