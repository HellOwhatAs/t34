use crate::game::TTT;

/// 2D 3x3 Tic Tac Toe game state represented as two bitboards.
/// The first u64 is the bitboard for player 0 (X), the second for player 1 (O).
/// A position is occupied if the corresponding bit is set in either player's bitboard.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
#[repr(transparent)]
pub struct TTT3x3(pub (u64, u64));

impl TTT for TTT3x3 {
    fn already_win(&self) -> Option<bool> {
        const WINNING_MASKS: [u64; 8] = [
            0b000000111, // rows
            0b000111000,
            0b111000000,
            0b001001001, // columns
            0b010010010,
            0b100100100,
            0b100010001, // diagonals
            0b001010100,
        ];

        let filled = self.0.0 | self.0.1;
        for &mask in WINNING_MASKS.iter() {
            if (filled & mask) != mask {
                continue;
            }
            if (self.0.0 & mask) == mask {
                return Some(false);
            }
            if (self.0.1 & mask) == mask {
                return Some(true);
            }
        }
        None
    }

    fn make_move(&self, role: bool, at: u32) -> Self {
        debug_assert_eq!(
            role,
            (self.0.0.count_ones() > self.0.1.count_ones()),
            "not your turn"
        );
        debug_assert!(
            (if role { self.0.1 } else { self.0.0 }) & (1 << at) == 0,
            "position already occupied"
        );
        Self(if role {
            (self.0.0, self.0.1 | 1 << at)
        } else {
            (self.0.0 | 1 << at, self.0.1)
        })
    }

    fn available_moves(&self) -> (bool, Vec<u32>) {
        let s = self.0.0 | self.0.1;
        (
            self.0.0.count_ones() > self.0.1.count_ones(),
            (0..9).filter(|i| s & (1 << i) == 0).collect::<Vec<_>>(),
        )
    }

    fn canonical_form(&self) -> Self {
        *self
    }
}
