mod builder;
mod compiler;
mod language;
mod parser;
mod readback;
mod rulebook;
mod runtime;

fn main() -> std::io::Result<()> {
  run_cli()?;
  //run_example()?;
  Ok(())
}

fn run_cli() -> std::io::Result<()> {
  let args: Vec<String> = std::env::args().collect();

  fn hvm(file: &str) -> String {
    if !file.ends_with(".hvm") {
      format!("{}.hvm", file)
    } else {
      file.to_string()
    }
  }

  if args.len() <= 1 {
    show_help();
    return Ok(());
  }

  let cmd = &args[1];

  if (cmd == "d" || cmd == "debug") && args.len() >= 3 {
    let file = &hvm(&args[2]);
    return run_code(&load_file_code(file), true);
  }

  if (cmd == "r" || cmd == "run") && args.len() >= 3 {
    let file = &hvm(&args[2]);
    return run_code(&load_file_code(file), false);
  }

  if (cmd == "c" || cmd == "compile") && args.len() >= 3 {
    let file = &hvm(&args[2]);
    return compile_code(&load_file_code(file), file);
  }

  println!("Invalid arguments: {:?}.", args);
  Ok(())
}

fn show_help() {
  println!("High-order Virtual Machine ({})", env!("CARGO_PKG_VERSION"));
  println!("==========================");
  println!();
  println!("To run a file, interpreted:");
  println!();
  println!("  hvm r file.hvm");
  println!();
  println!("To run a file in debug mode:");
  println!();
  println!("  hvm d file.hvm");
  println!();
  println!("To compile a file to C:");
  println!();
  println!("  hvm c file.hvm");
  println!();
  println!("This is a PROTOTYPE. Report bugs on https://github.com/Kindelia/HVM/issues!");
  println!();
}

fn make_call() -> language::Term {
  let pars = &std::env::args().collect::<Vec<String>>()[3..];
  let name = "Main".to_string();
  let args = pars.iter().map(|par| language::read_term(par)).collect();
  language::Term::Ctr { name, args }
}

fn run_code(code: &str, debug: bool) -> std::io::Result<()> {
  println!("Reducing.");
  let (norm, cost, size, time) = builder::eval_code(&make_call(), code, debug);
  println!("Rewrites: {} ({:.2} MR/s)", cost, (cost as f64) / (time as f64) / 1000.0);
  println!("Mem.Size: {}", size);
  println!();
  println!("{}", norm);
  Ok(())
}

fn compile_code(code: &str, name: &str) -> std::io::Result<()> {
  if !name.ends_with(".hvm") {
    panic!("Input file must end with .hvm.");
  }
  let name = format!("{}.go", &name[0..name.len() - 4]);
  compiler::compile_code_and_save(code, &name)?;
  println!("Compiled to '{}'.", name);
  Ok(())
}

fn load_file_code(file_name: &str) -> String {
  std::fs::read_to_string(file_name)
    .unwrap_or_else(|_| panic!("Error reading file: '{}'.", file_name))
}

#[allow(dead_code)]
fn run_example() -> std::io::Result<()> {
  // Source code
  let _code = "(Main) = (λf λx (f (f x)) λf λx (f (f x)))";

  let _code = "
    (Fn 0) = 1
    (Fn n) = (+ (Fn (- n 1)) (Fn (- n 1)))
    (Main) = (Fn 20)
  ";

  let _code = "
    // Applies a function to all elements in a list
    (Map fn (Nil))            = (Nil)
    (Map fn (Cons head tail)) = (Cons (fn head) (Map fn tail))

    // Increments all numbers on [1,2,3]
    (Main) = (Map λx(+ x 1) (Cons 1 (Cons 2 (Cons 3 (Nil)))))
  ";

  let _code = "
    (Filter fn (Cons x xs)) = (Filter_Cons (fn x) fn x xs)
      (Filter_Cons 1 fn x xs) = (Cons x (Filter fn xs))
      (Filter_Cons 0 fn x xs) = (Filter fn xs)
    (Filter fn (Nil)) = (Nil)

    (Concat (Nil) b)        = b
    (Concat (Cons ah at) b) = (Cons ah (Concat at b))

    (Quicksort (Nil)) = (Nil)
    (Quicksort (Cons h t)) =
      let min = (Filter λx(< x h) t)
      let max = (Filter λx(> x h) t)
      (Concat (Quicksort min) (Cons h (Quicksort max)))

    (Main) = (Quicksort (Cons 3 (Cons 1 (Cons 2 (Cons 4 (Nil))))))
  ";

  let code = "
    (Sort (Nil))                         = 0
    (Sort (Cons x Nil))                  = (Foo x)
    (Sort (Cons x (Cons y Nil)))         = (Foo x y)
    (Sort (Cons x (Cons y (Cons z zs)))) = (Foo x y z zs)
    (Foo (Bar 1 x) (Baz z k))            = (+ x z)
    (Foo (Bar 7 8) (Baz z k))            = 7
  ";

  // Compiles to C and saves as 'main.c'
  compiler::compile_code_and_save(code, "main.go")?;
  println!("Compiled to 'main.go'.");

  // Evaluates with interpreter

  println!("Reducing with interpreter.");
  let call = language::Term::Ctr { name: "Main".to_string(), args: Vec::new() };
  let (norm, cost, size, time) = builder::eval_code(&call, code, false);
  println!("Rewrites: {} ({:.2} MR/s)", cost, (cost as f64) / (time as f64) / 1000.0);
  println!("Mem.Size: {}", size);
  println!();
  println!("{}", norm);
  println!();

  Ok(())
}
