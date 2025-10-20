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

/// 2D 5x5_3 Tic Tac Toe game state represented as two bitboards.
/// The first u64 is the bitboard for player 0 (X), the second for player 1 (O).
/// A position is occupied if the corresponding bit is set in either player's bitboard.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
#[repr(transparent)]
pub struct TTT5x5_3(pub (u64, u64));

impl TTT for TTT5x5_3 {
    fn already_win(&self) -> Option<bool> {
        let xbb = self.0.0;
        let obb = self.0.1;
        let filled = xbb | obb;

        // Check rows for any 3-in-a-row
        for y in 0..5u32 {
            let base = y * 5;
            for x in 0..=2u32 {
                let mask =
                    (1u64 << (base + x)) | (1u64 << (base + x + 1)) | (1u64 << (base + x + 2));
                if (filled & mask) != mask {
                    continue;
                }
                if (xbb & mask) == mask {
                    return Some(false);
                }
                if (obb & mask) == mask {
                    return Some(true);
                }
            }
        }

        // Check columns for any 3-in-a-row
        for x in 0..5u32 {
            for y in 0..=2u32 {
                let i0 = y * 5 + x;
                let mask = (1u64 << i0) | (1u64 << (i0 + 5)) | (1u64 << (i0 + 10));
                if (filled & mask) != mask {
                    continue;
                }
                if (xbb & mask) == mask {
                    return Some(false);
                }
                if (obb & mask) == mask {
                    return Some(true);
                }
            }
        }

        // Check main diagonals (down-right) for any 3-in-a-row
        for y in 0..=2u32 {
            for x in 0..=2u32 {
                let i0 = y * 5 + x;
                let mask = (1u64 << i0) | (1u64 << (i0 + 6)) | (1u64 << (i0 + 12));
                if (filled & mask) != mask {
                    continue;
                }
                if (xbb & mask) == mask {
                    return Some(false);
                }
                if (obb & mask) == mask {
                    return Some(true);
                }
            }
        }

        // Check anti-diagonals (down-left) for any 3-in-a-row
        for y in 0..=2u32 {
            for x in 2..5u32 {
                let i0 = y * 5 + x;
                let mask = (1u64 << i0) | (1u64 << (i0 + 4)) | (1u64 << (i0 + 8));
                if (filled & mask) != mask {
                    continue;
                }
                if (xbb & mask) == mask {
                    return Some(false);
                }
                if (obb & mask) == mask {
                    return Some(true);
                }
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

/// 2D 10x10_5 Tic Tac Toe game state represented as two u128 bitboards (sufficient for 100 cells).
/// The first u128 is the bitboard for player 0 (X), the second for player 1 (O).
/// Win condition: any 5-in-a-row horizontally, vertically, or diagonally.
#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
#[repr(transparent)]
pub struct TTT10x10_5(pub (u128, u128));

impl TTT for TTT10x10_5 {
    fn already_win(&self) -> Option<bool> {
        let xbb = self.0.0;
        let obb = self.0.1;
        let filled = xbb | obb;

        // Rows: y in [0,9], x start in [0,5] (5 consecutive horizontally)
        for y in 0..10u32 {
            let base = y * 10;
            for x in 0..=5u32 {
                let mut mask = 0u128;
                for k in 0..5u32 {
                    mask |= 1u128 << (base + x + k);
                }
                if (filled & mask) != mask {
                    continue;
                }
                if (xbb & mask) == mask {
                    return Some(false);
                }
                if (obb & mask) == mask {
                    return Some(true);
                }
            }
        }

        // Columns: x in [0,9], y start in [0,5] (5 consecutive vertically)
        for x in 0..10u32 {
            for y in 0..=5u32 {
                let i0 = y * 10 + x;
                let mut mask = 0u128;
                for k in 0..5u32 {
                    mask |= 1u128 << (i0 + 10 * k);
                }
                if (filled & mask) != mask {
                    continue;
                }
                if (xbb & mask) == mask {
                    return Some(false);
                }
                if (obb & mask) == mask {
                    return Some(true);
                }
            }
        }

        // Main diagonals (down-right): starts x in [0,5], y in [0,5], step +11
        for y in 0..=5u32 {
            for x in 0..=5u32 {
                let i0 = y * 10 + x;
                let mut mask = 0u128;
                for k in 0..5u32 {
                    mask |= 1u128 << (i0 + 11 * k);
                }
                if (filled & mask) != mask {
                    continue;
                }
                if (xbb & mask) == mask {
                    return Some(false);
                }
                if (obb & mask) == mask {
                    return Some(true);
                }
            }
        }

        // Anti-diagonals (down-left): starts x in [4,9], y in [0,5], step +9
        for y in 0..=5u32 {
            for x in 4..10u32 {
                let i0 = y * 10 + x;
                let mut mask = 0u128;
                for k in 0..5u32 {
                    mask |= 1u128 << (i0 + 9 * k);
                }
                if (filled & mask) != mask {
                    continue;
                }
                if (xbb & mask) == mask {
                    return Some(false);
                }
                if (obb & mask) == mask {
                    return Some(true);
                }
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
            (if role { self.0.1 } else { self.0.0 }) & (1u128 << at) == 0,
            "position already occupied"
        );
        Self(if role {
            (self.0.0, self.0.1 | 1u128 << at)
        } else {
            (self.0.0 | 1u128 << at, self.0.1)
        })
    }

    fn available_moves(&self) -> (bool, Vec<u32>) {
        let s = self.0.0 | self.0.1;
        (
            self.0.0.count_ones() > self.0.1.count_ones(),
            (0..100)
                .filter(|i| s & (1u128 << i) == 0)
                .collect::<Vec<_>>(),
        )
    }

    fn canonical_form(&self) -> Self {
        // Helper to map a bitboard through a coordinate transform
        fn map_board<F: Fn(u32, u32) -> (u32, u32)>(bb: u128, f: &F) -> u128 {
            let mut out = 0u128;
            let mut i = 0u32;
            while i < 100u32 {
                if ((bb >> i) & 1u128) != 0 {
                    let x = i % 10;
                    let y = i / 10;
                    let (nx, ny) = f(x, y);
                    let ni = ny * 10 + nx;
                    out |= 1u128 << ni;
                }
                i += 1;
            }
            out
        }

        // Apply a transform to both players' bitboards
        fn apply<F: Fn(u32, u32) -> (u32, u32)>((xbb, obb): (u128, u128), f: &F) -> (u128, u128) {
            (map_board(xbb, f), map_board(obb, f))
        }

        let p = self.0;

        // Board size n = 10; indices 0..9
        let n1 = 9u32;

        // 8 symmetries: 4 rotations and those with a vertical reflection
        let t0 = apply(p, &|x, y| (x, y)); // identity
        let t1 = apply(p, &|x, y| (n1 - y, x)); // rot 90
        let t2 = apply(p, &|x, y| (n1 - x, n1 - y)); // rot 180
        let t3 = apply(p, &|x, y| (y, n1 - x)); // rot 270
        let t4 = apply(p, &|x, y| (n1 - x, y)); // mirror vertical
        let t5 = apply(p, &|x, y| (n1 - y, n1 - x)); // rot90 ∘ mirror vertical
        let t6 = apply(p, &|x, y| (x, n1 - y)); // rot180 ∘ mirror vertical
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

    #[test]
    fn ttt10x10_5_win_row_x() {
        // X has five in a row horizontally at row 0: (0,0)..(4,0)
        let x: u128 = (1u128 << 0) | (1u128 << 1) | (1u128 << 2) | (1u128 << 3) | (1u128 << 4);
        let s = TTT10x10_5((x, 0));
        assert_eq!(s.already_win(), Some(false));
    }

    #[test]
    fn ttt10x10_5_win_col_o() {
        // O has five in a column at x=9: (9,5)..(9,9)
        let o: u128 = (1u128 << 59) | (1u128 << 69) | (1u128 << 79) | (1u128 << 89) | (1u128 << 99);
        let s = TTT10x10_5((0, o));
        assert_eq!(s.already_win(), Some(true));
    }

    #[test]
    fn ttt10x10_5_win_diag_dr_x() {
        // X has five on main diagonal (down-right) starting at (2,2): 22,33,44,55,66
        let x: u128 = (1u128 << 22) | (1u128 << 33) | (1u128 << 44) | (1u128 << 55) | (1u128 << 66);
        let s = TTT10x10_5((x, 0));
        assert_eq!(s.already_win(), Some(false));
    }

    #[test]
    fn ttt10x10_5_win_diag_dl_o() {
        // O has five on anti-diagonal (down-left) starting at (8,1): 18,27,36,45,54
        let o: u128 = (1u128 << 18) | (1u128 << 27) | (1u128 << 36) | (1u128 << 45) | (1u128 << 54);
        let s = TTT10x10_5((0, o));
        assert_eq!(s.already_win(), Some(true));
    }

    #[test]
    fn ttt10x10_5_no_win_mixed() {
        // Mixed placements without forming five in a row
        // X has four in a row at row 0 but not five; O elsewhere
        let x: u128 = (1u128 << 0) | (1u128 << 1) | (1u128 << 2) | (1u128 << 3);
        let o: u128 = (1u128 << 20) | (1u128 << 21) | (1u128 << 22);
        let s = TTT10x10_5((x, o));
        assert_eq!(s.already_win(), None);
    }

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
    #[test]
    fn ttt5x5_3_win_row_x() {
        // X has three in a row horizontally at (0,0), (1,0), (2,0)
        let x: u64 = (1 << 0) | (1 << 1) | (1 << 2);
        let s = TTT5x5_3((x, 0));
        assert_eq!(s.already_win(), Some(false));
    }

    #[test]
    fn ttt5x5_3_win_col_o() {
        // O has three in a column at (4,1), (4,2), (4,3)
        let o: u64 = (1 << 9) | (1 << 14) | (1 << 19);
        let s = TTT5x5_3((0, o));
        assert_eq!(s.already_win(), Some(true));
    }

    #[test]
    fn ttt5x5_3_win_diag_dr_x() {
        // X has three on main diagonal at (1,1), (2,2), (3,3)
        let x: u64 = (1 << 6) | (1 << 12) | (1 << 18);
        let s = TTT5x5_3((x, 0));
        assert_eq!(s.already_win(), Some(false));
    }

    #[test]
    fn ttt5x5_3_win_diag_dl_o() {
        // O has three on anti-diagonal at (3,1), (2,2), (1,3)
        let o: u64 = (1 << 8) | (1 << 12) | (1 << 16);
        let s = TTT5x5_3((0, o));
        assert_eq!(s.already_win(), Some(true));
    }

    #[test]
    fn ttt5x5_3_no_win_mixed() {
        // Mixed placements, no three-in-a-row by either player
        // Row 0: X at (0,0), O at (1,0) blocks any horizontal three
        // Diagonal has only two X's (0,0) and (1,1)
        let x: u64 = (1 << 0) | (1 << 6);
        let o: u64 = (1 << 1) | (1 << 5);
        let s = TTT5x5_3((x, o));
        assert_eq!(s.already_win(), None);
    }
}
