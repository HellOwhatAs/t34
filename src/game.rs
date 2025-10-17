pub trait T3Game: Copy {
    fn already_win(&self) -> Option<bool>;
    fn make_move(&self, role: bool, at: u32) -> Self;
    fn available_moves(&self) -> (bool, Vec<u32>);
}

pub const WINNING_MASKS: [u64; 76] = all_winning_masks();

/// 3D 4x4x4 Tic Tac Toe game state represented as two bitboards.
/// The first u64 is the bitboard for player 0 (X), the second for player 1 (O).
/// A position is occupied if the corresponding bit is set in either player's bitboard.
impl T3Game for (u64, u64) {
    fn already_win(&self) -> Option<bool> {
        let filled = self.0 | self.1;
        for &mask in WINNING_MASKS.iter() {
            if (filled & mask) != mask {
                continue;
            }
            if (self.0 & mask) == mask {
                return Some(false);
            }
            if (self.1 & mask) == mask {
                return Some(true);
            }
        }
        None
    }

    fn make_move(&self, role: bool, at: u32) -> (u64, u64) {
        debug_assert_eq!(
            role,
            (self.0.count_ones() > self.1.count_ones()),
            "not your turn"
        );
        debug_assert!(
            (if role { self.1 } else { self.0 }) & (1 << at) == 0,
            "position already occupied"
        );
        if role {
            (self.0, self.1 | 1 << at)
        } else {
            (self.0 | 1 << at, self.1)
        }
    }

    fn available_moves(&self) -> (bool, Vec<u32>) {
        let s = self.0 | self.1;
        (
            self.0.count_ones() > self.1.count_ones(),
            (0..u64::BITS)
                .filter(|i| s & (1 << i) == 0)
                .collect::<Vec<_>>(),
        )
    }
}

pub const fn pos2idx(x: u32, y: u32, z: u32) -> u32 {
    debug_assert!(x < 4 && y < 4 && z < 4);
    x * 16 + y * 4 + z
}

pub const fn idx2pos(idx: u32) -> (u32, u32, u32) {
    debug_assert!(idx < 64);
    let x = idx / 16;
    let y = (idx % 16) / 4;
    let z = idx % 4;
    (x, y, z)
}

#[test]
fn test_pos_idx_pos() {
    (0..4)
        .flat_map(|x| (0..4).flat_map(move |y| (0..4).map(move |z| (x, y, z))))
        .enumerate()
        .for_each(|(i, (x, y, z))| {
            let idx = pos2idx(x, y, z);
            let (x2, y2, z2) = idx2pos(idx);
            assert_eq!((x, y, z), (x2, y2, z2));
            assert_eq!(i as u32, idx);
        });
}

const fn all_winning_masks() -> [u64; 76] {
    let mut res = [0; 76];
    let mut i = 0;
    let mut a = 0;
    while a < 4 {
        let mut b = 0;
        while b < 4 {
            res[i] = (1u64 << pos2idx(a, b, 0))
                | (1u64 << pos2idx(a, b, 1))
                | (1u64 << pos2idx(a, b, 2))
                | (1u64 << pos2idx(a, b, 3));
            i += 1;
            res[i] = (1u64 << pos2idx(a, 0, b))
                | (1u64 << pos2idx(a, 1, b))
                | (1u64 << pos2idx(a, 2, b))
                | (1u64 << pos2idx(a, 3, b));
            i += 1;
            res[i] = (1u64 << pos2idx(0, a, b))
                | (1u64 << pos2idx(1, a, b))
                | (1u64 << pos2idx(2, a, b))
                | (1u64 << pos2idx(3, a, b));
            i += 1;
            b += 1;
        }
        a += 1;
    }
    let mut a = 0;
    while a < 4 {
        res[i] = (1u64 << pos2idx(a, 0, 0))
            | (1u64 << pos2idx(a, 1, 1))
            | (1u64 << pos2idx(a, 2, 2))
            | (1u64 << pos2idx(a, 3, 3));
        i += 1;
        res[i] = (1u64 << pos2idx(a, 0, 3))
            | (1u64 << pos2idx(a, 1, 2))
            | (1u64 << pos2idx(a, 2, 1))
            | (1u64 << pos2idx(a, 3, 0));
        i += 1;
        res[i] = (1u64 << pos2idx(0, a, 0))
            | (1u64 << pos2idx(1, a, 1))
            | (1u64 << pos2idx(2, a, 2))
            | (1u64 << pos2idx(3, a, 3));
        i += 1;
        res[i] = (1u64 << pos2idx(0, a, 3))
            | (1u64 << pos2idx(1, a, 2))
            | (1u64 << pos2idx(2, a, 1))
            | (1u64 << pos2idx(3, a, 0));
        i += 1;
        res[i] = (1u64 << pos2idx(0, 0, a))
            | (1u64 << pos2idx(1, 1, a))
            | (1u64 << pos2idx(2, 2, a))
            | (1u64 << pos2idx(3, 3, a));
        i += 1;
        res[i] = (1u64 << pos2idx(0, 3, a))
            | (1u64 << pos2idx(1, 2, a))
            | (1u64 << pos2idx(2, 1, a))
            | (1u64 << pos2idx(3, 0, a));
        i += 1;
        a += 1;
    }
    res[i] = (1u64 << pos2idx(0, 0, 0))
        | (1u64 << pos2idx(1, 1, 1))
        | (1u64 << pos2idx(2, 2, 2))
        | (1u64 << pos2idx(3, 3, 3));
    i += 1;
    res[i] = (1u64 << pos2idx(0, 0, 3))
        | (1u64 << pos2idx(1, 1, 2))
        | (1u64 << pos2idx(2, 2, 1))
        | (1u64 << pos2idx(3, 3, 0));
    i += 1;
    res[i] = (1u64 << pos2idx(0, 3, 0))
        | (1u64 << pos2idx(1, 2, 1))
        | (1u64 << pos2idx(2, 1, 2))
        | (1u64 << pos2idx(3, 0, 3));
    i += 1;
    res[i] = (1u64 << pos2idx(0, 3, 3))
        | (1u64 << pos2idx(1, 2, 2))
        | (1u64 << pos2idx(2, 1, 1))
        | (1u64 << pos2idx(3, 0, 0));
    res
}

#[test]
fn test_winning_masks() {
    use std::collections::HashSet;
    assert!(
        WINNING_MASKS
            .iter()
            .to_owned()
            .collect::<HashSet<_>>()
            .len()
            == WINNING_MASKS.len(),
        "winning masks are not unique"
    );
    for mask in WINNING_MASKS {
        assert_eq!(mask.count_ones(), 4);
        let mut points = vec![];
        for i in 0..64 {
            if mask & (1 << i) != 0 {
                let (x, y, z) = idx2pos(i);
                assert!(x < 4 && y < 4 && z < 4);
                points.push((x, y, z));
            }
        }
        assert_eq!(points.len(), 4);
        for i in 0..4 {
            for j in i + 1..4 {
                let (x1, y1, z1) = points[i];
                let (x2, y2, z2) = points[j];
                assert!(
                    x1 == x2
                        || y1 == y2
                        || z1 == z2
                        || (x1 as i32 - x2 as i32).abs() == (y1 as i32 - y2 as i32).abs()
                            && (y1 as i32 - y2 as i32).abs() == (z1 as i32 - z2 as i32).abs(),
                    "points {:?} are not aligned",
                    points
                );
            }
        }
    }
}
