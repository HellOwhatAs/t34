pub trait TTT {
    fn already_win(&self) -> Option<bool>;
    fn make_move(&self, role: bool, at: u32) -> Self;
    fn available_moves(&self) -> (bool, Vec<u32>);
    fn canonical_form(&self) -> Self;
}
