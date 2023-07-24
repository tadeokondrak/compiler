use super::root::{Root, TokenKind, TreeId, TreeKind};

#[derive(Clone, Copy, Debug)]
enum Event {
    Open(TreeKind),
    Token,
    Error(&'static str),
    Close,
}

#[derive(Default)]
struct Builder {
    events: Vec<Event>,
}

struct MarkOpen(usize);

struct MarkClosed(usize);

impl Builder {
    pub fn open(&mut self) -> MarkOpen {
        let i = self.events.len();
        self.events.push(Event::Open(TreeKind::INVALID));
        MarkOpen(i)
    }

    pub fn open_before(&mut self, MarkClosed(i): MarkClosed) -> MarkOpen {
        self.events.insert(i, Event::Open(TreeKind::INVALID));
        MarkOpen(i)
    }

    pub fn close(&mut self, kind: TreeKind, MarkOpen(i): MarkOpen) -> MarkClosed {
        self.events[i] = Event::Open(kind);
        self.events.push(Event::Close);
        MarkClosed(i)
    }

    pub fn error(&mut self, message: &'static str) {
        self.events.push(Event::Error(message));
    }

    pub fn token(&mut self) {
        self.events.push(Event::Token);
    }

    pub fn build(
        &self,
        src: &str,
        tokens: &[TokenKind],
        token_lengths: &[usize],
        token_is_trivia: impl Fn(TokenKind) -> bool,
    ) -> Root {
        let mut text = String::new();
        //let mut token_kinds = Vec::new();
        //let mut token_text_ranges = Vec::new();
        //let mut token_trivia_ranges = Vec::new();
        let mut tree_kinds = Vec::new();
        let mut tree_children_ranges = Vec::new();
        //let mut tree_children_data = Vec::new();
        //let mut trivia_kinds = Vec::new();
        //let mut trivia_counts = Vec::new();
        for &event in &self.events {
            match event {
                Event::Open(kind) => {
                    let tree_id = TreeId(u32_from_usize(tree_kinds.len()));
                    tree_kinds.push(kind);
                    tree_children_ranges.push((0, 0));
                }
                Event::Token => {}
                Event::Error(error) => {}
                Event::Close => {}
            }
        }
        todo!()
    }
}

fn u32_from_usize(n: usize) -> u32 {
    n as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builder() {
        let mut builder = Builder::default();
        let m = builder.open();
        builder.token();
        builder.close(TreeKind(0), m);
        eprintln!("{:?}", builder.events);
    }
}
