use crate::game3d::{idx2pos, pos2idx};

const PERMS: [[u8; 3]; 6] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
];

pub fn iter_canonicals(state: (u64, u64)) -> impl Iterator<Item = (u64, u64)> {
    PERMS.iter().flat_map(move |&perm| {
        (0..8u8)
            .into_iter()
            .map(move |flips| apply_transform_pair(state, perm, flips))
    })
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

#[test]
fn empty_board_single() {
    let res: std::collections::HashSet<(u64, u64)> = iter_canonicals((0, 0)).collect();
    assert_eq!(res.len(), 1);
    assert!(res.contains(&(0, 0)), "Empty board missing from canonicals");
}

#[test]
fn identity_present_and_counts_preserved() {
    let x = 1u64 << pos2idx(1, 2, 3);
    let o = 1u64 << pos2idx(0, 0, 0);
    let s = (x, o);
    let res: std::collections::HashSet<(u64, u64)> = iter_canonicals(s).collect();
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
    let res1: std::collections::HashSet<(u64, u64)> = iter_canonicals(s1).collect();

    let s2 = (
        (1u64 << pos2idx(1, 1, 0)) | (1u64 << pos2idx(3, 0, 3)),
        (1u64 << pos2idx(0, 3, 0)) | (1u64 << pos2idx(3, 0, 2)),
    );
    let res2: std::collections::HashSet<(u64, u64)> = iter_canonicals(s2).collect();

    assert_eq!(res1, res2, "Canonicals sets do not match");
}
