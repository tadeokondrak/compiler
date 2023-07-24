use crate::root::{NodeKind, Root, TokenId, TreeId, TreeKind, TokenKind};
use std::{cell::Cell, ptr::NonNull, sync::Arc};
use text_size::TextRange;

#[derive(Clone, Debug)]
pub enum Node {
    Tree(Tree),
    Token(Token),
}

#[derive(Clone, Debug)]
pub struct Tree {
    data: NonNull<TreeData>,
}

#[derive(Clone, Debug)]
pub struct Token {
    data: NonNull<TokenData>,
}

struct TreeData {
    rc: Cell<u32>,
    tree: TreeId,
    root: NonNull<Root>,
    parent: Option<NonNull<TreeData>>,
}

struct TokenData {
    rc: Cell<u32>,
    token: TokenId,
    root: NonNull<Root>,
    parent: NonNull<TreeData>,
}

impl Drop for Tree {
    fn drop(&mut self) {
        unsafe {
            let data = self.data.as_ref();
            data.rc.set(data.rc.get() - 1);
            if data.rc.get() == 0 {
                drop(Box::from_raw(self.data.as_ptr()));
            }
        }
    }
}

impl Drop for Token {
    fn drop(&mut self) {
        unsafe {
            let data = self.data.as_ref();
            data.rc.set(data.rc.get() - 1);
            if data.rc.get() == 0 {
                drop(Box::from_raw(self.data.as_ptr()));
            }
        }
    }
}

impl Drop for TreeData {
    fn drop(&mut self) {
        unsafe {
            match self.parent {
                Some(self_parent) => {
                    let parent = self_parent.as_ref();
                    parent.rc.set(parent.rc.get() - 1);
                    if parent.rc.get() == 0 {
                        drop(Box::from_raw(self_parent.as_ptr()));
                    }
                }
                None => {
                    drop(Arc::from_raw(self.root.as_ptr()));
                }
            }
        }
    }
}

impl Drop for TokenData {
    fn drop(&mut self) {
        unsafe {
            let parent = self.parent.as_ref();
            parent.rc.set(parent.rc.get() - 1);
            if parent.rc.get() == 0 {
                drop(Box::from_raw(self.parent.as_ptr()));
            }
        }
    }
}

impl Tree {
    fn new(root: Arc<Root>) -> Tree {
        unsafe {
            let data = TreeData {
                rc: Cell::new(1),
                tree: TreeId(0),
                root: NonNull::new_unchecked(Arc::into_raw(root).cast_mut()),
                parent: None,
            };
            Tree {
                data: NonNull::new_unchecked(Box::into_raw(Box::new(data))),
            }
        }
    }

    pub fn kind(&self) -> TreeKind {
        unsafe {
            let data = self.data.as_ref();
            let root = data.root.as_ref();
            root.tree_kind(data.tree)
        }
    }

    pub fn parent(&self) -> Option<Tree> {
        unsafe {
            let data = self.data.as_ref();
            let parent = data.parent?.as_ref();
            parent.rc.set(parent.rc.get() + 1);
            Some(Tree {
                data: NonNull::from(parent),
            })
        }
    }

    fn children(&self) -> impl Iterator<Item = Tree> {
        [].into_iter()
    }

    fn children_with_tokens(&self) -> impl Iterator<Item = Node> {
        [].into_iter()
    }

    fn ancestors(&self) -> impl Iterator<Item = Tree> {
        [].into_iter()
    }

    fn descendants(&self) -> impl Iterator<Item = Tree> {
        [].into_iter()
    }

    fn descendants_with_tokens(&self) -> impl Iterator<Item = Node> {
        [].into_iter()
    }

    fn text_range(&self) -> TextRange {
        todo!()
    }
}

impl Token {
    pub fn kind(&self) -> TokenKind {
        unsafe {
            let data = self.data.as_ref();
            let root = data.root.as_ref();
            root.token_kind(data.token)
        }
    }

    pub fn text(&self) -> &str {
        unsafe {
            let data = self.data.as_ref();
            let root = data.root.as_ref();
            root.token_text(data.token)
        }
    }

    pub fn parent(&self) -> Tree {
        unsafe {
            let data = self.data.as_ref();
            let parent = data.parent.as_ref();
            parent.rc.set(parent.rc.get() + 1);
            Tree {
                data: NonNull::from(parent),
            }
        }
    }

    fn leading_trivia(&self) -> () {}

    fn trailing_trivia(&self) -> () {}

    fn text_range(&self) -> TextRange {
        todo!()
    }

    fn ancestors(&self) -> impl Iterator<Item = Tree> {
        [].into_iter()
    }
}

impl Node {
    pub fn kind(&self) -> NodeKind {
        match self {
            Node::Tree(it) => NodeKind::Tree(it.kind()),
            Node::Token(it) => NodeKind::Token(it.kind()),
        }
    }

    fn parent(&self) -> Option<Tree> {
        todo!()
    }

    fn ancestors(&self) -> impl Iterator<Item = Tree> {
        let first = match self {
            Node::Tree(it) => it.clone(),
            Node::Token(it) => it.parent(),
        };
        std::iter::successors(Some(first), Tree::parent)
    }

    fn text_range(&self) -> TextRange {
        match self {
            Node::Tree(tree) => tree.text_range(),
            Node::Token(token) => token.text_range(),
        }
    }
}
