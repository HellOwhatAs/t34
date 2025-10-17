pub mod canonical;
pub mod game;
pub mod game2d;
pub mod game3d;

use game::TTT;
use game2d::TTT3x3;
// use game3d::TTT4x4x4;
use dashmap::DashMap;
use rayon::prelude::*;

fn minmax<T>(state: T, cache: &DashMap<T, (Option<u32>, i32, usize)>) -> (Option<u32>, i32, usize)
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

    if let Some(cached) = cache.get(&state) {
        return *cached;
    }

    let mut best_move = None;
    let mut best_score = if player { -1 } else { 1 };
    let mut best_depth = 0;

    let results = moves
        .par_iter()
        .map(|&m| (m, minmax(state.make_move(player, m), cache)))
        .collect::<Vec<_>>();

    for (m, (_, score, depth)) in results {
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
    cache.insert(state, res);
    res
}

fn main() {
    fn print_state(state: TTT3x3) {
        for x in 0..3 {
            for y in 0..3 {
                let idx = x * 3 + y;
                let c = if (state.0.0 & (1 << idx)) != 0 {
                    'X'
                } else if (state.0.1 & (1 << idx)) != 0 {
                    'O'
                } else {
                    idx.to_string().chars().next().unwrap()
                };
                print!("{}", c);
            }
            println!();
        }
    }
    fn wait_input() -> u32 {
        use std::io::{self, Write};
        loop {
            print!("Enter your move: ");
            io::stdout().flush().unwrap();
            let mut input = String::new();
            io::stdin().read_line(&mut input).unwrap();
            if let Ok(num) = input.trim().parse::<u32>() {
                if num < 9 {
                    return num;
                }
            }
            println!("Invalid input, please enter a number between 0 and 8.");
        }
    }
    let cache = DashMap::new();
    let mut state = TTT3x3((0, 0));
    loop {
        print_state(state);
        let mv = wait_input();
        state = state.make_move(false, mv);
        if state.already_win().is_some() {
            print_state(state);
            println!("You win!");
            break;
        }
        let (m, s, d) = minmax(state, &cache);
        if s > 0 {
            println!("You'll lose in {} moves.", d);
        }
        state = state.make_move(true, m.unwrap());
        if state.already_win().is_some() {
            print_state(state);
            println!("AI wins!");
            break;
        }
    }
}
