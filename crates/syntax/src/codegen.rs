use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::{collections::HashMap, str::FromStr};
use ungrammar::{Grammar, Node, Rule};

const ASCII_NAMES: [&str; 128] = [
    "null",
    "start of heading",
    "start of text",
    "end of text",
    "end of transmission",
    "enquiry",
    "acknowledge",
    "bell",
    "backspace",
    "character tabulation",
    "line feed",
    "line tabulation",
    "form feed",
    "carriage return",
    "shift out",
    "shift in",
    "data link escape",
    "device control one",
    "device control two",
    "device control three",
    "device control four",
    "negative acknowledge",
    "synchronous idle",
    "end of transmission block",
    "cancel",
    "end of medium",
    "substitute",
    "escape",
    "information separator four",
    "information separator three",
    "information separator two",
    "information separator one",
    "space",
    "exclamation mark",
    "quotation mark",
    "number sign",
    "dollar sign",
    "percent sign",
    "ampersand",
    "apostrophe",
    "left parenthesis",
    "right parenthesis",
    "asterisk",
    "plus sign",
    "comma",
    "hyphen minus",
    "full stop",
    "solidus",
    "digit zero",
    "digit one",
    "digit two",
    "digit three",
    "digit four",
    "digit five",
    "digit six",
    "digit seven",
    "digit eight",
    "digit nine",
    "colon",
    "semicolon",
    "less than sign",
    "equals sign",
    "greater than sign",
    "question mark",
    "commercial at",
    "latin capital letter a",
    "latin capital letter b",
    "latin capital letter c",
    "latin capital letter d",
    "latin capital letter e",
    "latin capital letter f",
    "latin capital letter g",
    "latin capital letter h",
    "latin capital letter i",
    "latin capital letter j",
    "latin capital letter k",
    "latin capital letter l",
    "latin capital letter m",
    "latin capital letter n",
    "latin capital letter o",
    "latin capital letter p",
    "latin capital letter q",
    "latin capital letter r",
    "latin capital letter s",
    "latin capital letter t",
    "latin capital letter u",
    "latin capital letter v",
    "latin capital letter w",
    "latin capital letter x",
    "latin capital letter y",
    "latin capital letter z",
    "left square bracket",
    "reverse solidus",
    "right square bracket",
    "circumflex accent",
    "low line",
    "grave accent",
    "latin small letter a",
    "latin small letter b",
    "latin small letter c",
    "latin small letter d",
    "latin small letter e",
    "latin small letter f",
    "latin small letter g",
    "latin small letter h",
    "latin small letter i",
    "latin small letter j",
    "latin small letter k",
    "latin small letter l",
    "latin small letter m",
    "latin small letter n",
    "latin small letter o",
    "latin small letter p",
    "latin small letter q",
    "latin small letter r",
    "latin small letter s",
    "latin small letter t",
    "latin small letter u",
    "latin small letter v",
    "latin small letter w",
    "latin small letter x",
    "latin small letter y",
    "latin small letter z",
    "left curly bracket",
    "vertical line",
    "right curly bracket",
    "tilde",
    "delete",
];

#[rustfmt::skip]
const PUNCTUATION_TOKENS: &[&str] = &[
    "!", "!=",
    "#",
    "$",
    "%", "%=",
    "&", "&=",
    "(",
    ")",
    "*", "*=",
    "+", "+=",
    ",",
    "-", "-=",
    ".",
    "/", "/=",
    ":",
    ";",
    "<", "<<", "<<=", "<=",
    "=", "==",
    ">", ">=", ">>", ">>=",
    "?",
    "@",
    "[",
    "\\",
    "]",
    "^", "^=",
    "_",
    "{",
    "|", "|=",
    "}",
    "~",
];

#[rustfmt::skip]
const KEYWORDS: &[&str] = &[
    "break",
    "const",
    "continue",
    "deref",
    "else",
    "enum",
    "fn",
    "if",
    "let",
    "loop",
    "ptr",
    "ref",
    "return",
    "slice",
    "struct",
    "union",
    "variant",
    "while",
];

#[derive(Debug)]
struct AstEnum {
    name: String,
    variants: Vec<String>,
}

#[derive(Debug)]
struct AstNode {
    name: String,
    nodes: Vec<(String, String)>,
    tokens: Vec<String>,
    children: Vec<(String, String)>,
}

#[test]
fn test_gen() {
    let grammar = Grammar::from_str(include_str!("ast.ungram")).unwrap();

    let mut ast_enums = Vec::new();
    let mut ast_nodes = Vec::new();

    for node in grammar.iter() {
        if let Some(ast_enum) = ast_enum(&grammar, node) {
            ast_enums.push(ast_enum);
        } else {
            ast_nodes.push(ast_node(&grammar, node));
        }
    }

    let (syntax, syntax_map) = gen_syntax(ast_nodes.iter().map(|node| node.name.clone()));

    let syntax_map = &syntax_map;
    let nodes = ast_nodes.iter().map(|ast_node| {
        let name = format_ident!("{}", ast_node.name);
        let kind = format_ident!("{}", ast_node.name);
        quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct #name {
                pub(super) node: SyntaxNode,
            }
            #[rustfmt::skip]
            impl AstNode for #name {
                type Language = Language;
                fn can_cast(kind: Syntax) -> bool {
                    kind == Syntax::#kind
                }
                fn cast(node: SyntaxNode) -> Option<#name> {
                    if #name::can_cast(node.kind()) {
                        Some(#name { node })
                    } else {
                        None
                    }
                }
                fn syntax(&self) -> &SyntaxNode {
                    &self.node
                }
            }
        }
    });

    let node_impls = ast_nodes.iter().map(|ast_node| {
        let name = format_ident!("{}", ast_node.name);
        let nodes = ast_node
            .nodes
            .iter()
            .filter(|_| ast_node.name != "BinaryExpr" && ast_node.name != "IfExpr")
            .map(|(label, kind)| {
                let name = format_ident!("{}", label);
                let kind = format_ident!("{kind}");
                quote! {
                    pub fn #name(&self) -> Option<#kind> {
                        child(&self.node)
                    }
                }
            });

        let tokens = ast_node
            .tokens
            .iter()
            .filter(|_| ast_node.name != "BinaryExpr")
            .map(|kind| {
                let kind = syntax_map.get(kind).unwrap_or(kind);
                let name = snake_case(kind);
                let name = format_ident!(
                    "{}{}",
                    name,
                    name.ends_with("_keyword").then_some("").unwrap_or("_token")
                );
                let kind = format_ident!("{kind}");
                quote! {
                    pub fn #name(&self) -> Option<SyntaxToken> {
                        token(&self.node, Syntax::#kind)
                    }
                }
            });

        let children = ast_node.children.iter().map(|(label, kind)| {
            let name = format_ident!("{}", &label);
            let kind = format_ident!("{kind}");
            quote! {
                pub fn #name(&self) -> AstChildren<#kind> {
                    children(&self.node)
                }
            }
        });

        quote! {
            #[rustfmt::skip]
            impl #name {
                #(#nodes)*
                #(#tokens)*
                #(#children)*
            }
        }
    });

    let enums = ast_enums.iter().map(|ast_enum| {
        let name = format_ident!("{}", ast_enum.name);

        let variants = ast_enum
            .variants
            .iter()
            .map(|variant| format_ident!("{variant}"));

        let def = {
            let variants = variants.clone().map(|variant| {
                quote! { #variant(#variant), }
            });
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                pub enum #name {
                    #(#variants)*
                }
            }
        };

        let imp = {
            let can_cast = {
                let variants = variants.clone();
                quote! { matches!(kind, #(Syntax::#variants)|*) }
            };

            let cast = {
                let arms = variants.clone().map(|variant| {
                    quote! {
                        Syntax::#variant => Some(#name::#variant(#variant { node })),
                    }
                });
                quote! {
                    match node.kind() {
                        #(#arms)*
                        _ => None,
                    }
                }
            };

            let syntax = {
                let arms = variants.clone().map(|variant| {
                    quote! {
                        #name::#variant(#variant { node }) => node,
                    }
                });
                quote! { match self { #(#arms)* } }
            };

            quote! {
                #[rustfmt::skip]
                impl AstNode for #name {
                    type Language = Language;
                    fn can_cast(kind: Syntax) -> bool {
                        #can_cast
                    }
                    fn cast(node: SyntaxNode) -> Option<#name> {
                        #cast
                    }
                    fn syntax(&self) -> &SyntaxNode {
                        #syntax
                    }
                }
            }
        };

        quote! {
            #def
            #imp
        }
    });

    let ast_nodes = quote! {
        use crate::{ast::*, AstChildren, AstNode, Language, Syntax, SyntaxNode, SyntaxToken};
        use rowan::ast::support::{child, children, token};
        #(#nodes)*
        #(#node_impls)*
    };

    let ast_enums = quote! {
        use crate::{ast::*, AstNode, Language, Syntax, SyntaxNode};
        #(#enums)*
    };

    let mut changed = false;

    changed |= write_fenced(
        concat!(env!("CARGO_MANIFEST_DIR"), "/src/lib.rs"),
        gen_syntax_macro(&syntax),
    );

    changed |= write(
        concat!(env!("CARGO_MANIFEST_DIR"), "/src/generated/syntax.rs"),
        gen_syntax_enum(&syntax, &syntax_map),
    );

    changed |= write(
        concat!(env!("CARGO_MANIFEST_DIR"), "/src/generated/ast_nodes.rs"),
        ast_nodes,
    );

    changed |= write(
        concat!(env!("CARGO_MANIFEST_DIR"), "/src/generated/ast_enums.rs"),
        ast_enums,
    );

    if changed {
        panic!("generated code changed; rerun tests");
    }
}

fn ast_enum(grammar: &Grammar, node: Node) -> Option<AstEnum> {
    let Rule::Alt(alt) = &grammar[node].rule else {
        return None;
    };

    let nodes = alt
        .iter()
        .map(|rule| match rule {
            &Rule::Node(node) => Some(node),
            _ => None,
        })
        .collect::<Option<Vec<Node>>>()?;

    let name = grammar[node].name.clone();
    let variants = nodes
        .into_iter()
        .map(|node| grammar[node].name.clone())
        .collect();

    Some(AstEnum { name, variants })
}

fn ast_node(grammar: &Grammar, node: Node) -> AstNode {
    let name = grammar[node].name.clone();
    let mut nodes = Vec::new();
    let mut tokens = Vec::new();
    let mut children = Vec::new();

    fn collect(
        grammar: &Grammar,
        nodes: &mut Vec<(String, String)>,
        tokens: &mut Vec<String>,
        children: &mut Vec<(String, String)>,
        rule: &Rule,
        many: bool,
        label: Option<&str>,
    ) {
        match rule {
            Rule::Labeled { label, rule } => {
                assert!(!many);
                collect(grammar, nodes, tokens, children, rule, false, Some(label));
            }
            &Rule::Node(node) => {
                let name = grammar[node].name.clone();
                if many {
                    let label = label
                        .map(|s| s.to_owned())
                        .unwrap_or_else(|| inflect_plural(&snake_case(&name)));
                    children.push((label, name));
                } else {
                    let label = label
                        .map(|s| s.to_owned())
                        .unwrap_or_else(|| snake_case(&name));
                    nodes.push((label, name));
                }
            }
            &Rule::Token(token) => {
                assert!(!many);
                tokens.push(grammar[token].name.clone());
            }
            Rule::Seq(rules) | Rule::Alt(rules) => {
                assert!(!many);
                for rule in rules {
                    collect(grammar, nodes, tokens, children, rule, false, None);
                }
            }
            Rule::Opt(rule) => {
                assert!(!many);
                collect(grammar, nodes, tokens, children, rule, false, label);
            }
            Rule::Rep(rule) => {
                assert!(!many);
                collect(grammar, nodes, tokens, children, rule, true, None);
            }
        }
    }

    collect(
        grammar,
        &mut nodes,
        &mut tokens,
        &mut children,
        &grammar[node].rule,
        false,
        None,
    );

    AstNode {
        name,
        nodes,
        tokens,
        children,
    }
}

fn gen_syntax(
    nodes: impl Iterator<Item = String>,
) -> (Vec<(Option<String>, String)>, HashMap<String, String>) {
    let mut syntax = Vec::new();
    syntax.extend_from_slice(&[
        (Some("eof".to_string()), "Eof".to_string()),
        (Some("error".to_string()), "Error".to_string()),
        (Some("comment".to_string()), "Comment".to_string()),
        (Some("space".to_string()), "Space".to_string()),
        (Some("newline".to_string()), "Newline".to_string()),
        (Some("number".to_string()), "Number".to_string()),
        (Some("string".to_string()), "String".to_string()),
        (Some("character".to_string()), "Character".to_string()),
        (Some("identifier".to_string()), "Identifier".to_string()),
    ]);
    syntax.extend(PUNCTUATION_TOKENS.iter().map(|token| {
        let mut name = String::new();
        for c in token.chars() {
            if !name.is_empty() {
                name.push(' ');
            }
            name.push_str(ASCII_NAMES[c as usize]);
        }
        (Some(token.to_string()), upper_camel_case(&name))
    }));
    syntax.extend(KEYWORDS.iter().map(|token| {
        (
            Some(token.to_string()),
            upper_camel_case(&token) + "Keyword",
        )
    }));
    syntax.extend(nodes.map(|node_name| (None, node_name)));
    let syntax_map: HashMap<String, String> = syntax
        .iter()
        .filter_map(|(token, name)| Some((token.as_ref()?.clone(), name.clone())))
        .collect();
    (syntax, syntax_map)
}

fn gen_syntax_enum(
    syntax: &[(Option<String>, String)],
    syntax_map: &HashMap<String, String>,
) -> TokenStream {
    let variants = syntax.iter().map(|(_, name)| {
        let name = format_ident!("{name}");
        quote! {
            #name,
        }
    });
    let last_syntax = format_ident!("{}", syntax.last().unwrap().1);
    let from_punct_str = {
        let arms = PUNCTUATION_TOKENS.iter().map(|&punct| {
            let name = format_ident!("{}", &syntax_map[punct]);
            quote! {
                #punct => Some(Syntax::#name),
            }
        });

        quote! {
            pub(crate) fn from_punct_str(s: &str) -> Option<Syntax> {
                match s {
                    #(#arms)*
                    _ => None,
                }
            }
        }
    };
    let from_keyword_str = {
        let arms = KEYWORDS.iter().map(|&punct| {
            let name = format_ident!("{}", &syntax_map[punct]);
            quote! {
                #punct => Some(Syntax::#name),
            }
        });

        quote! {
            pub(crate) fn from_keyword_str(s: &str) -> Option<Syntax> {
                match s {
                    #(#arms)*
                    _ => None,
                }
            }
        }
    };
    let decompose_n = (2..=3).map(|n| {
        let arms = syntax
            .iter()
            .filter_map(|(token, name)| Some((token.as_ref()?, name)))
            .filter(|(token, _name)| token.len() == n)
            .filter(|(token, _name)| token.chars().all(|c| !c.is_ascii_alphanumeric()))
            .map(|(token, name)| {
                let mut buf = [0u8];
                let elements = token
                    .chars()
                    .map(|c| &syntax_map[c.encode_utf8(&mut buf)])
                    .map(|name| format_ident!("{name}"))
                    .map(|name| quote!(Syntax::#name));
                let name = format_ident!("{name}");
                quote! {
                    Syntax::#name => Some([#(#elements),*]),
                }
            });
        let name = format_ident!("decompose_{n}");
        quote! {
            #[rustfmt::skip]
            pub(crate) fn #name(self) -> Option<[Syntax; #n]> {
                match self {
                    #(#arms)*
                    _ => None,
                }
            }
        }
    });
    quote! {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr(u16)]
        pub enum Syntax {
            #(#variants)*
        }

        impl Syntax {
            pub(crate) const LAST: Syntax = Syntax::#last_syntax;
            #from_punct_str
            #from_keyword_str
            #(#decompose_n)*
        }
    }
}

fn gen_syntax_macro(syntax: &[(Option<String>, String)]) -> TokenStream {
    let arms = syntax
        .iter()
        .filter_map(|(token, name)| Some((token.as_ref()?, name)))
        .map(|(token, name)| {
            let name = format_ident!("{name}");
            quote! {
                (#token) => ($crate::Syntax::#name);
            }
        });
    quote! {
        #[macro_export]
        #[rustfmt::skip]
        macro_rules! t {
            #(#arms)*
        }
    }
}

fn upper_camel_case(s: &str) -> String {
    let mut out = String::new();
    let mut upper = true;
    for c in s.chars() {
        if c == ' ' {
            upper = true;
        } else {
            out.push(if upper { c.to_ascii_uppercase() } else { c });
            upper = false;
        }
    }
    out
}

fn snake_case(s: &str) -> String {
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_ascii_uppercase() && i > 0 {
            out.push('_');
        }
        out.push(c.to_ascii_lowercase());
    }
    out
}

fn inflect_plural(s: &str) -> String {
    format!("{s}s")
}

fn write(filename: &str, src: TokenStream) -> bool {
    let src = prettyplease::unparse(&syn::parse2(src).unwrap());
    let existing_content = std::fs::read_to_string(filename).unwrap();
    let new_content = src;
    if new_content != existing_content {
        std::fs::write(filename, new_content).unwrap();
        true
    } else {
        false
    }
}

fn write_fenced(filename: &str, src: TokenStream) -> bool {
    let src = prettyplease::unparse(&syn::parse2(src).unwrap());
    const START: &str = "// <generated>\n";
    const END: &str = "// </generated>\n";
    let existing_content = std::fs::read_to_string(filename).unwrap();
    let (before, rest) = existing_content.split_once(START).unwrap();
    let (_, after) = rest.split_once(END).unwrap();
    let new_content = format!("{before}{START}{src}{END}{after}");
    if new_content != existing_content {
        std::fs::write(filename, new_content).unwrap();
        true
    } else {
        false
    }
}
