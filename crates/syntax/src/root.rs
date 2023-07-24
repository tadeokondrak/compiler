use std::ptr::NonNull;

#[derive(Clone, Copy, Debug)]
enum TriviaKind {
    Tab,
    Space,
    Newline,
}

#[derive(Clone, Copy, Debug)]
pub struct TreeKind(pub(crate) u16);

#[derive(Clone, Copy, Debug)]
pub struct TokenKind(pub(crate) u16);

pub enum NodeKind {
    Tree(TreeKind),
    Token(TokenKind),
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct PackedNodeKind(u16);

#[derive(Clone, Copy, Debug)]
pub(crate) struct TreeId(pub(crate) u32);

#[derive(Clone, Copy, Debug)]
pub(crate) struct TokenId(pub(crate) u32);

enum NodeId {
    Tree(TreeId),
    Token(TokenId),
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct PackedNodeId(u32);

impl TreeKind {
    pub(crate) const INVALID: TreeKind = TreeKind(!0);
}

impl TokenKind {
    pub(crate) const INVALID: TokenKind = TokenKind(!0);
}

impl PackedNodeKind {
    const TREE_FLAG: u16 = 1 << 15;
}

impl PackedNodeId {
    const TREE_FLAG: u32 = 1 << 31;
}

impl From<NodeKind> for PackedNodeKind {
    fn from(value: NodeKind) -> PackedNodeKind {
        match value {
            NodeKind::Tree(TreeKind(kind)) => PackedNodeKind(kind & PackedNodeKind::TREE_FLAG),
            NodeKind::Token(TokenKind(kind)) => PackedNodeKind(kind),
        }
    }
}

impl From<PackedNodeKind> for NodeKind {
    fn from(PackedNodeKind(packed): PackedNodeKind) -> NodeKind {
        if packed & PackedNodeKind::TREE_FLAG != 0 {
            NodeKind::Tree(TreeKind(packed & !PackedNodeKind::TREE_FLAG))
        } else {
            NodeKind::Token(TokenKind(packed))
        }
    }
}

impl From<TokenKind> for PackedNodeKind {
    fn from(TokenKind(token_kind): TokenKind) -> Self {
        debug_assert!(token_kind & PackedNodeKind::TREE_FLAG == 0);
        PackedNodeKind(token_kind)
    }
}

impl From<TreeKind> for PackedNodeKind {
    fn from(TreeKind(tree_kind): TreeKind) -> Self {
        debug_assert!(tree_kind & PackedNodeKind::TREE_FLAG == 0);
        PackedNodeKind(tree_kind | PackedNodeKind::TREE_FLAG)
    }
}

impl From<TokenId> for PackedNodeId {
    fn from(TokenId(token_id): TokenId) -> Self {
        debug_assert!(token_id & PackedNodeId::TREE_FLAG == 0);
        PackedNodeId(token_id)
    }
}

impl From<TreeId> for PackedNodeId {
    fn from(TreeId(tree_id): TreeId) -> Self {
        debug_assert!(tree_id & PackedNodeId::TREE_FLAG == 0);
        PackedNodeId(tree_id | PackedNodeId::TREE_FLAG)
    }
}

impl TreeKind {
    fn from_u16(v: u16) -> TreeKind {
        assert!(v & 1 << 15 == 0);
        TreeKind(v)
    }
}

impl TokenKind {
    fn from_u16(v: u16) -> TokenKind {
        assert!(v & 1 << 15 == 0);
        TokenKind(v)
    }
}

#[derive(Debug)]
pub(crate) struct Root {
    text: Box<str>,
    token_count: u32,
    token_kinds: NonNull<TokenKind>,
    token_text_ranges: NonNull<(u32, u32)>,        // pos, len
    token_trivia_ranges: NonNull<(u32, u32, u32)>, // pos, leading, trailing
    tree_count: u32,
    tree_kinds: NonNull<TreeKind>,
    tree_children_ranges: NonNull<(u32, u32)>, // pos, len
    tree_children_data: NonNull<PackedNodeId>,
    trivia_count: u32,
    trivia_kinds: NonNull<TriviaKind>,
    trivia_counts: NonNull<u8>,
}

impl Root {
    pub(crate) fn token_kind(&self, TokenId(token): TokenId) -> TokenKind {
        assert!(token < self.token_count);
        unsafe { *self.token_kinds.as_ptr().add(token as usize) }
    }

    pub(crate) fn token_text(&self, TokenId(token): TokenId) -> &str {
        assert!(token < self.token_count);
        let (start, len) = unsafe { *self.token_text_ranges.as_ptr().add(token as usize) };
        let end = start + len;
        &self.text[start as usize..end as usize]
    }

    pub(crate) fn tree_kind(&self, TreeId(tree): TreeId) -> TreeKind {
        assert!(tree < self.tree_count);
        unsafe { *self.tree_kinds.as_ptr().add(tree as usize) }
    }

    pub(crate) fn tree_children(&self, TreeId(tree): TreeId) -> &[PackedNodeId] {
        unsafe {
            let (start, len) = *self.tree_children_ranges.as_ptr().add(tree as usize);
            let start_ptr = self.tree_children_data.as_ptr().add(start as usize);
            std::slice::from_raw_parts(start_ptr, len as usize)
        }
    }
}

impl Drop for Root {
    fn drop(&mut self) {
        unsafe fn drop_slice<T>(count: u32, slice: NonNull<T>) {
            drop(Box::from_raw(std::ptr::slice_from_raw_parts_mut(
                slice.as_ptr(),
                count as usize,
            )));
        }

        unsafe {
            drop_slice(self.token_count, self.token_kinds);
            drop_slice(self.token_count, self.token_text_ranges);
            drop_slice(self.token_count, self.token_trivia_ranges);
            drop_slice(self.tree_count, self.tree_kinds);
            drop_slice(self.tree_count, self.tree_children_ranges);
            drop_slice(self.tree_count, self.tree_children_data);
            drop_slice(self.trivia_count, self.trivia_kinds);
            drop_slice(self.trivia_count, self.trivia_counts);
        }
    }
}
