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

/// 2D 5x5 Tic Tac Toe game state represented as two bitboards.
/// The first u64 is the bitboard for player 0 (X), the second for player 1 (O).
/// A position is occupied if the corresponding bit is set in either player's bitboard.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
#[repr(transparent)]
pub struct TTT4x4(pub (u64, u64));

impl TTT for TTT4x4 {
    fn already_win(&self) -> Option<bool> {
        const WINNING_MASKS: [u64; 10] = [
            0b0000000000001111, // rows
            0b0000000011110000,
            0b0000111100000000,
            0b1111000000000000,
            0b0001000100010001, // columns
            0b0010001000100010,
            0b0100010001000100,
            0b1000100010001000,
            0b1000010000100001, // diagonals
            0b0001001001001000,
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
            (0..16).filter(|i| s & (1 << i) == 0).collect::<Vec<_>>(),
        )
    }

    fn canonical_form(&self) -> Self {
        // Helper to map a bitboard through a coordinate transform
        fn map_board<F: Fn(u32, u32) -> (u32, u32)>(bb: u64, f: &F) -> u64 {
            let mut out = 0u64;
            let mut i = 0u32;
            while i < 16u32 {
                if ((bb >> i) & 1u64) != 0 {
                    let x = i % 4;
                    let y = i / 4;
                    let (nx, ny) = f(x, y);

                    let ni = ny * 4 + nx;
                    out |= 1u64 << ni;
                }
                i += 1;
            }
            out
        }

        // Apply a transform to both players' bitboards
        fn apply<F: Fn(u32, u32) -> (u32, u32)>((xbb, obb): (u64, u64), f: &F) -> (u64, u64) {
            (map_board(xbb, f), map_board(obb, f))
        }

        let p = self.0;

        // 8 symmetries: 4 rotations and those with a vertical reflection
        let t0 = apply(p, &|x, y| (x, y)); // identity
        let t1 = apply(p, &|x, y| (3u32 - y, x)); // rot 90
        let t2 = apply(p, &|x, y| (3u32 - x, 3u32 - y)); // rot 180
        let t3 = apply(p, &|x, y| (y, 3u32 - x)); // rot 270
        let t4 = apply(p, &|x, y| (3u32 - x, y)); // mirror vertical
        let t5 = apply(p, &|x, y| (3u32 - y, 3u32 - x)); // rot90 ∘ mirror vertical
        let t6 = apply(p, &|x, y| (x, 3u32 - y)); // rot180 ∘ mirror vertical
        let t7 = apply(p, &|x, y| (y, x)); // rot270 ∘ mirror vertical (main diagonal)

        // Pick lexicographically minimal (X bits first, then O bits)
        let mut minp = t0;
        for cand in [t1, t2, t3, t4, t5, t6, t7] {
            if cand.0 < minp.0 || (cand.0 == minp.0 && cand.1 < minp.1) {
                minp = cand;
            }
        }

        Self(minp)
    }
}

/// 2D 5x5 Tic Tac Toe game state represented as two bitboards.
/// The first u64 is the bitboard for player 0 (X), the second for player 1 (O).
/// A position is occupied if the corresponding bit is set in either player's bitboard.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
#[repr(transparent)]
pub struct TTT5x5(pub (u64, u64));

impl TTT for TTT5x5 {
    fn already_win(&self) -> Option<bool> {
        const WINNING_MASKS: [u64; 12] = [
            0b0000000000000000000011111, // rows
            0b0000000000000001111100000,
            0b0000000000111110000000000,
            0b0000011111000000000000000,
            0b1111100000000000000000000,
            0b0000100001000010000100001, // columns
            0b0001000010000100001000010,
            0b0010000100001000010000100,
            0b0100001000010000100001000,
            0b1000010000100001000010000,
            0b1000001000001000001000001, // diagonals
            0b0000100010001000100010000,
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
            (0..25).filter(|i| s & (1 << i) == 0).collect::<Vec<_>>(),
        )
    }

    fn canonical_form(&self) -> Self {
        // Helper to map a bitboard through a coordinate transform
        fn map_board<F: Fn(u32, u32) -> (u32, u32)>(bb: u64, f: &F) -> u64 {
            let mut out = 0u64;
            let mut i = 0u32;
            while i < 25u32 {
                if ((bb >> i) & 1u64) != 0 {
                    let x = i % 5;
                    let y = i / 5;
                    let (nx, ny) = f(x, y);

                    let ni = ny * 5 + nx;
                    out |= 1u64 << ni;
                }
                i += 1;
            }
            out
        }

        // Apply a transform to both players' bitboards
        fn apply<F: Fn(u32, u32) -> (u32, u32)>((xbb, obb): (u64, u64), f: &F) -> (u64, u64) {
            (map_board(xbb, f), map_board(obb, f))
        }

        let p = self.0;

        // 8 symmetries: 4 rotations and those with a vertical reflection
        let t0 = apply(p, &|x, y| (x, y)); // identity
        let t1 = apply(p, &|x, y| (4u32 - y, x)); // rot 90
        let t2 = apply(p, &|x, y| (4u32 - x, 4u32 - y)); // rot 180
        let t3 = apply(p, &|x, y| (y, 4u32 - x)); // rot 270
        let t4 = apply(p, &|x, y| (4u32 - x, y)); // mirror vertical
        let t5 = apply(p, &|x, y| (4u32 - y, 4u32 - x)); // rot90 ∘ mirror vertical
        let t6 = apply(p, &|x, y| (x, 4u32 - y)); // rot180 ∘ mirror vertical
        let t7 = apply(p, &|x, y| (y, x)); // rot270 ∘ mirror vertical (main diagonal)

        // Pick lexicographically minimal (X bits first, then O bits)
        let mut minp = t0;
        for cand in [t1, t2, t3, t4, t5, t6, t7] {
            if cand.0 < minp.0 || (cand.0 == minp.0 && cand.1 < minp.1) {
                minp = cand;
            }
        }

        Self(minp)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn map_board<F: Fn(u32, u32) -> (u32, u32)>(bb: u64, f: &F) -> u64 {
        let mut out = 0u64;
        let mut i = 0u32;
        while i < 25u32 {
            if ((bb >> i) & 1u64) != 0 {
                let x = i % 5;
                let y = i / 5;
                let (nx, ny) = f(x, y);
                let ni = ny * 5 + nx;
                out |= 1u64 << ni;
            }
            i += 1;
        }
        out
    }

    fn apply<F: Fn(u32, u32) -> (u32, u32)>(p: (u64, u64), f: &F) -> (u64, u64) {
        (map_board(p.0, f), map_board(p.1, f))
    }

    #[test]
    fn canonical_idempotent() {
        let x: u64 = (1 << 0) | (1 << 7) | (1 << 12) | (1 << 18) | (1 << 24);
        let o: u64 = (1 << 3) | (1 << 5) | (1 << 9) | (1 << 20);
        let s = TTT5x5((x, o));
        let c = s.canonical_form();
        assert_eq!(c, c.canonical_form());
    }

    #[test]
    fn canonical_invariant_under_symmetry() {
        let x: u64 = (1 << 0) | (1 << 7) | (1 << 12) | (1 << 18) | (1 << 24);
        let o: u64 = (1 << 3) | (1 << 5) | (1 << 9) | (1 << 20);
        let p = (x, o);
        let base = TTT5x5(p).canonical_form();
        let variants = [
            apply(p, &|x, y| (x, y)),
            apply(p, &|x, y| (4u32 - y, x)),
            apply(p, &|x, y| (4u32 - x, 4u32 - y)),
            apply(p, &|x, y| (y, 4u32 - x)),
            apply(p, &|x, y| (4u32 - x, y)),
            apply(p, &|x, y| (4u32 - y, 4u32 - x)),
            apply(p, &|x, y| (x, 4u32 - y)),
            apply(p, &|x, y| (y, x)),
        ];
        for v in variants {
            assert_eq!(TTT5x5(v).canonical_form(), base);
        }
    }

    #[test]
    fn canonical_tiebreak_on_o_when_x_equal() {
        // X is empty so tie-break should fall back to minimal O among symmetries.
        let s = TTT5x5((0, 1 << (0 * 5 + 4))); // O at (4,0)
        let expected = TTT5x5((0, 1 << (0 * 5 + 0))); // should map to (0,0)
        assert_eq!(s.canonical_form(), expected);
    }

    #[test]
    fn canonical_single_bit_x_minimization() {
        // O is empty; minimal X under symmetries should be (0,0) when starting from (4,0).
        let s = TTT5x5((1 << (0 * 5 + 4), 0)); // X at (4,0)
        let expected = TTT5x5((1 << (0 * 5 + 0), 0)); // should map to (0,0)
        assert_eq!(s.canonical_form(), expected);
    }
}
