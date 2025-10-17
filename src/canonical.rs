use crate::game::{idx2pos, pos2idx};

const PERMS: [[u8; 3]; 6] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
];

pub fn min_canonicals(state: (u64, u64)) -> (u64, u64) {
    let mut res = state;
    for perm in PERMS {
        for flips in 0u8..8u8 {
            let s = apply_transform_pair(state, perm, flips);
            if s < res {
                res = s;
            }
        }
    }
    res
}

#[inline]
const fn apply_transform_pair(s: (u64, u64), perm: [u8; 3], flips: u8) -> (u64, u64) {
    (
        apply_transform_board(s.0, perm, flips),
        apply_transform_board(s.1, perm, flips),
    )
}

#[inline]
const fn apply_transform_board(board: u64, perm: [u8; 3], flips: u8) -> u64 {
    if board == 0 {
        return 0;
    }
    let mut out: u64 = 0;
    let mut b = board;
    while b != 0 {
        let i = b.trailing_zeros();
        b &= b - 1;

        let (x, y, z) = idx2pos(i);
        let coords = [x, y, z];

        let nx = map_axis(coords[perm[0] as usize], (flips & 0b001) != 0);
        let ny = map_axis(coords[perm[1] as usize], (flips & 0b010) != 0);
        let nz = map_axis(coords[perm[2] as usize], (flips & 0b100) != 0);

        let ni = pos2idx(nx, ny, nz);
        out |= 1u64 << ni;
    }
    out
}

#[inline]
const fn map_axis(v: u32, flip: bool) -> u32 {
    if flip { 3 - v } else { v }
}

#[cfg(test)]
fn __all_canonicals(state: (u64, u64)) -> std::collections::HashSet<(u64, u64)> {
    let mut uniq = std::collections::HashSet::with_capacity(48);
    for perm in PERMS {
        for flips in 0u8..8u8 {
            let s = apply_transform_pair(state, perm, flips);
            uniq.insert(s);
        }
    }
    uniq
}

#[test]
fn empty_board_single() {
    let res = __all_canonicals((0, 0));
    assert_eq!(res.len(), 1);
    assert!(res.contains(&(0, 0)), "Empty board missing from canonicals");
}

#[test]
fn identity_present_and_counts_preserved() {
    let x = 1u64 << pos2idx(1, 2, 3);
    let o = 1u64 << pos2idx(0, 0, 0);
    let s = (x, o);
    let res = __all_canonicals(s);
    assert!(res.contains(&s), "Original state missing from canonicals");
    for (a, b) in &res {
        assert_eq!(a.count_ones(), 1);
        assert_eq!(b.count_ones(), 1);
        assert_eq!((*a | *b).count_ones(), 2);
        assert_eq!((*a & *b), 0);
    }
}

#[test]
fn test_min_canonical() {
    let s1 = (
        (1u64 << pos2idx(1, 2, 3)) | (1u64 << pos2idx(0, 0, 0)),
        (1u64 << pos2idx(3, 3, 3)) | (1u64 << pos2idx(0, 0, 1)),
    );
    let res1 = __all_canonicals(s1);

    let s2 = (
        (1u64 << pos2idx(1, 1, 0)) | (1u64 << pos2idx(3, 0, 3)),
        (1u64 << pos2idx(0, 3, 0)) | (1u64 << pos2idx(3, 0, 2)),
    );
    let res2 = __all_canonicals(s2);

    assert_eq!(res1, res2, "Canonicals sets do not match");
}
