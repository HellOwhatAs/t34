pub mod canonical;
pub mod game;
pub mod game2d;
pub mod game3d;

use dashmap::DashMap;
use game::TTT;
use game2d::{TTT3x3, TTT4x4, TTT5x5};
use game3d::TTT4x4x4;
use rayon::prelude::*;

fn minmax<T>(state: T, cache: &DashMap<T, (i32, usize)>) -> (Option<u32>, i32, usize)
where
    T: game::TTT + Eq + core::hash::Hash + std::marker::Sync + std::marker::Send,
{
    if let Some(winner) = state.already_win() {
        return if winner { (None, 1, 0) } else { (None, -1, 0) };
    }
    let (player, moves) = state.available_moves();
    if moves.is_empty() {
        return (None, 0, 0);
    }

    let mut best_move = None;
    let mut best_score = if player { -1 } else { 1 };
    let mut best_depth = 0;

    let results = moves
        .par_iter()
        .map(|&m| {
            let new_state = state.make_move(player, m);
            if let Some(cached) = cache.get(&new_state.canonical_form()) {
                (m, *cached)
            } else {
                let res = minmax(new_state, cache);
                (m, (res.1, res.2))
            }
        })
        .collect::<Vec<_>>();

    for (m, (score, depth)) in results {
        // wants max score when player, min score when !player
        // prefer faster win, slower loss
        if (player && (score > best_score) || !player && (score < best_score))
            || (score == best_score
                && (if player && (score > 0) || !player && (score < 0) {
                    depth < best_depth
                } else {
                    depth > best_depth
                }))
        {
            best_score = score;
            best_move = Some(m);
            best_depth = depth;
        }
    }

    let res = (best_move, best_score, best_depth + 1);
    cache.insert(state.canonical_form(), (res.1, res.2));
    res
}

#[test]
fn test_3x3() {
    let cache = DashMap::new();
    let mut state = TTT3x3((0, 0));
    state = state.make_move(false, 0);
    state = state.make_move(true, 2);
    state = state.make_move(false, 1);
    state = state.make_move(true, 4);
    state = state.make_move(false, 3);
    let (m, s, d) = minmax(state, &cache);
    println!("{:?} {:?}, {:?}", m, s, d);
}

fn print_state_2d(state: (u64, u64), n: i32) {
    let mut grid = vec![];
    let mut max_width = 0;
    for x in 0..n {
        grid.push(vec![]);
        for y in 0..n {
            let idx = x * n + y;
            let c = if (state.0 & (1 << idx)) != 0 {
                "X".to_owned()
            } else if (state.1 & (1 << idx)) != 0 {
                "O".to_owned()
            } else {
                idx.to_string()
            };
            max_width = max_width.max(c.len());
            grid.last_mut().unwrap().push(c);
        }
    }
    for row in grid {
        let line = row
            .into_iter()
            .map(|c| format!("{:>width$}", c, width = max_width))
            .collect::<Vec<_>>()
            .join(" | ");
        println!("{}", line);
        println!("{}", "-".repeat(line.len()));
    }
}
fn wait_input(max: u32) -> u32 {
    use std::io::{self, Write};
    loop {
        print!("Enter your move: ");
        io::stdout().flush().unwrap();
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        if let Ok(num) = input.trim().parse::<u32>() {
            if num < max {
                return num;
            }
        }
        println!("Invalid input, please enter a number between 0 and 8.");
    }
}

fn main() {
    let cache = DashMap::new();
    let mut state = TTT4x4((0, 0));
    loop {
        print_state_2d(state.0, 4);
        let mv = wait_input(16);
        state = state.make_move(false, mv);
        if state.already_win().is_some() {
            print_state_2d(state.0, 4);
            println!("You win!");
            break;
        }
        let (m, s, d) = minmax(state, &cache);
        println!("{:?} {:?} {:?}", m, s, d);
        if let Some(m) = m {
            if s > 0 {
                println!("You'll lose in {} moves.", d);
            }
            state = state.make_move(true, m);
            if state.already_win().is_some() {
                print_state_2d(state.0, 4);
                println!("AI wins!");
                break;
            }
        } else {
            println!("It's a draw!");
            break;
        }
    }
}

#[test]
fn test_struct_name() {
    struct Name {}
    let res = std::any::type_name::<Name>();
    impl Name {
        fn get_name(&self) -> &'static str {
            std::any::type_name::<Self>()
        }
    }
    let res2 = (Name {}).get_name().rfind("m");
    println!("{:?} {:?}", res, res2);
}
