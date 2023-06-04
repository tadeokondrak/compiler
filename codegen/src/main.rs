use heck::ToSnakeCase;
use std::{
    collections::HashMap,
    error::Error,
    fmt::Write,
    io::{self, Read},
    slice,
    str::FromStr,
};
use ungrammar::{Grammar, NodeData, Rule};

fn token_name(name: &str) -> &str {
    match name {
        "(" => "l_paren",
        ")" => "r_paren",
        "{" => "l_brace",
        "}" => "r_brace",
        "+" => "plus",
        "*" => "star",
        "fn" => "kw_fn",
        "const" => "kw_const",
        "return" => "kw_return",
        "=" => "eq",
        other => other,
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut input = String::new();
    io::stdin().lock().read_to_string(&mut input).unwrap();
    let grammar = Grammar::from_str(&input).unwrap();

    let mut output = String::new();
    writeln!(output, "const syntax = @import(\"syntax.zig\");")?;

    for node in grammar.iter().map(|i| &grammar[i]) {
        match &node.rule {
            labeled @ Rule::Labeled { .. } => {
                tree_wrapper(&mut output, &grammar, node, slice::from_ref(labeled))?;
            }
            Rule::Seq(seq) => {
                tree_wrapper(&mut output, &grammar, node, seq)?;
            }
            Rule::Alt(alt) => {
                writeln!(
                    output,
                    "pub const {name} = union(enum) {{",
                    name = node.name
                )?;
                let mut variants = Vec::new();
                let mut accessors = Vec::new();
                for rule in alt {
                    match rule {
                        Rule::Labeled { label, rule } => {
                            let Rule::Node(node) = **rule else { todo!() };
                            variants.push((label, node));
                        }
                        Rule::Token(token) => {
                            accessors.push(token);
                        }
                        _ => unimplemented!(),
                    }
                }
                for (label, node) in &variants {
                    writeln!(output, "{label}: {name},", name = grammar[*node].name)?;
                }
                writeln!(
                    output,
                    "pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {{"
                )?;
                writeln!(output, "return switch (root.treeTag(tree)) {{",)?;
                for (label, node) in &variants {
                    writeln!(
                        output,
                        ".{name} => .{{ .{label} = .{{ .tree = tree }} }},",
                        name = grammar[*node].name.to_snake_case()
                    )?;
                }
                writeln!(output, "else => null,")?;
                writeln!(output, "}};")?;
                writeln!(output, "}}")?;
                for token in accessors {
                    writeln!(
                        output,
                        "pub fn {name}(this: @This(), root: syntax.Root) ?syntax.Token \
                        {{ return syntax.findToken(root, this.tree, .{name}); }}",
                        name = token_name(&grammar[*token].name),
                    )?;
                }

                writeln!(output, "}};")?;
            }
            Rule::Token(_token) => {
                writeln!(output, "pub const {name} = struct {{", name = node.name)?;
                writeln!(output, "token: syntax.Tree,")?;
                // TODO
                writeln!(output, "}};")?;
            }
            other => unimplemented!("{other:?}"),
        }
    }

    println!("{}", output);

    Ok(())
}

fn tree_wrapper(
    output: &mut String,
    grammar: &Grammar,
    node: &NodeData,
    seq: &[Rule],
) -> Result<(), Box<dyn Error>> {
    writeln!(output, "pub const {name} = struct {{", name = node.name)?;
    writeln!(output, "tree: syntax.Tree,")?;
    writeln!(
        output,
        "pub fn cast(root: syntax.Root, tree: syntax.Tree) ?@This() {{"
    )?;
    writeln!(
        output,
        "return syntax.castTree(root, tree, .{name}, @This());",
        name = node.name.to_snake_case()
    )?;
    writeln!(output, "}}")?;
    let mut counts = HashMap::new();
    for rule in seq {
        match rule {
            Rule::Labeled { label, rule } => match **rule {
                Rule::Node(node) => {
                    let n = counts
                        .entry(&grammar[node].name)
                        .and_modify(|n: &mut u32| *n += 1)
                        .or_default();
                    writeln!(
                        output,
                        "pub fn {label}(this: @This(), root: syntax.Root) ?{name} \
                            {{ return syntax.findNthTree(root, this.tree, {name}, {n}); }}",
                        name = grammar[node].name,
                        label = label,
                    )?;
                }
                Rule::Token(token) => {
                    writeln!(
                        output,
                        "pub fn {label}(this: @This(), root: syntax.Root) ?syntax.Token \
                            {{ return syntax.findToken(root, this.tree, .{name}); }}",
                        name = token_name(&grammar[token].name),
                        label = label,
                    )?;
                }
                ref other => todo!("{other:?}"),
            },
            Rule::Token(token) => {
                writeln!(
                    output,
                    "pub fn {name}(this: @This(), root: syntax.Root) ?syntax.Token \
                        {{ return syntax.findToken(root, this.tree, .{name}); }}",
                    name = token_name(&grammar[*token].name),
                )?;
            }
            _ => unimplemented!("{rule:?}"),
        }
    }
    writeln!(output, "}};")?;
    Ok(())
}
