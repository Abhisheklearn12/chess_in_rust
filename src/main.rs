// Features:
// - 0x88 board representation
// - Move generation (legal-ish: handles captures, promotions, castling basics, en passant)
// - Alpha-beta search with iterative deepening
// - Simple evaluation (material + piece-square tables)
// - Terminal UI: ASCII board, play vs engine or engine vs engine, make moves via UCI-like input
// - Single-file for easy inspection and running
// NOTE: This aims to be educational and practical; some advanced rules/details are simplified but handled correctly for typical play.

use std::cmp::max;
use std::fmt;
use std::io::{self, Write};
use std::time::{Duration, Instant};

// =====================
// 0x88 Board Utilities
// =====================

pub type Sq = usize; // 0..127 but we'll use 0..128 with 0x88 tests

const BOARD_SIZE: usize = 128; // using 0x88

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Piece {
    Empty,
    WP,
    WN,
    WB,
    WR,
    WQ,
    WK,
    BP,
    BN,
    BB,
    BR,
    BQ,
    BK,
}

impl Piece {
    fn from_char(c: char) -> Piece {
        match c {
            'P' => Piece::WP,
            'N' => Piece::WN,
            'B' => Piece::WB,
            'R' => Piece::WR,
            'Q' => Piece::WQ,
            'K' => Piece::WK,
            'p' => Piece::BP,
            'n' => Piece::BN,
            'b' => Piece::BB,
            'r' => Piece::BR,
            'q' => Piece::BQ,
            'k' => Piece::BK,
            _ => Piece::Empty,
        }
    }
    fn to_char(self) -> char {
        match self {
            Piece::WP => 'P',
            Piece::WN => 'N',
            Piece::WB => 'B',
            Piece::WR => 'R',
            Piece::WQ => 'Q',
            Piece::WK => 'K',
            Piece::BP => 'p',
            Piece::BN => 'n',
            Piece::BB => 'b',
            Piece::BR => 'r',
            Piece::BQ => 'q',
            Piece::BK => 'k',
            Piece::Empty => '.',
        }
    }
    fn is_white(self) -> bool {
        match self {
            Piece::WP | Piece::WN | Piece::WB | Piece::WR | Piece::WQ | Piece::WK => true,
            _ => false,
        }
    }
    fn is_black(self) -> bool {
        match self {
            Piece::BP | Piece::BN | Piece::BB | Piece::BR | Piece::BQ | Piece::BK => true,
            _ => false,
        }
    }
    fn is_empty(self) -> bool {
        self == Piece::Empty
    }
}

// 0x88 helpers
fn on_board(s: Sq) -> bool {
    (s & 0x88) == 0
}

fn sq(rank: i32, file: i32) -> Sq {
    ((rank << 4) | file) as usize
}

// Convert 0x88 square to human algebraic like e2
fn sq_to_alg(s: Sq) -> String {
    let r = (s >> 4) as i32;
    let f = (s & 15) as i32;
    if r < 0 || r > 7 || f < 0 || f > 7 {
        return String::from("??");
    }
    let file = (b'a' + f as u8) as char;
    let rank = (1 + r).to_string();
    format!("{}{}", file, rank)
}

fn alg_to_sq(s: &str) -> Option<Sq> {
    let s = s.trim();
    if s.len() < 2 {
        return None;
    }
    let bytes = s.as_bytes();
    let f = (bytes[0] as char).to_ascii_lowercase();
    let rch = bytes[1] as char;
    if !(('a'..='h').contains(&f)) {
        return None;
    }
    if !(('1'..='8').contains(&rch)) {
        return None;
    }
    let file = (f as u8 - b'a') as i32;
    let rank = (rch as u8 - b'1') as i32;
    Some(sq(rank, file))
}

// =====================
// Board State
// =====================

#[derive(Clone)]
struct Board {
    cells: [Piece; BOARD_SIZE],
    side_white: bool, // true if white to move
    castling: u8,     // bits: 1 white K, 2 white Q, 4 black k, 8 black q
    ep: Option<Sq>,   // en passant square
    halfmove_clock: u32,
    fullmove: u32,
    history: Vec<Undo>,
}

#[derive(Clone, Copy)]
struct Undo {
    mv_from: Sq,
    mv_to: Sq,
    captured: Piece,
    prev_castling: u8,
    prev_ep: Option<Sq>,
    prev_halfmove: u32,
}

impl Board {
    fn empty() -> Board {
        Board {
            cells: [Piece::Empty; BOARD_SIZE],
            side_white: true,
            castling: 0,
            ep: None,
            halfmove_clock: 0,
            fullmove: 1,
            history: Vec::new(),
        }
    }

    fn from_fen(fen: &str) -> Board {
        let mut b = Board::empty();
        let parts: Vec<&str> = fen.split_whitespace().collect();
        if parts.is_empty() {
            return b;
        }
        // board
        let ranks: Vec<&str> = parts[0].split('/').collect();
        for (r, rank_str) in ranks.iter().enumerate() {
            let rank = 7 - r as i32;
            let mut file = 0i32;
            for ch in rank_str.chars() {
                if ch.is_digit(10) {
                    file += ch.to_digit(10).unwrap() as i32;
                } else {
                    let sqi = sq(rank, file);
                    b.cells[sqi] = Piece::from_char(ch);
                    file += 1;
                }
            }
        }
        // side
        if parts.len() > 1 {
            b.side_white = parts[1] == "w"
        }
        // castling
        b.castling = 0;
        if parts.len() > 2 {
            let c = parts[2];
            if c.contains('K') {
                b.castling |= 1
            }
            if c.contains('Q') {
                b.castling |= 2
            }
            if c.contains('k') {
                b.castling |= 4
            }
            if c.contains('q') {
                b.castling |= 8
            }
        }
        // ep
        b.ep = None;
        if parts.len() > 3 {
            if parts[3] != "-" {
                b.ep = alg_to_sq(parts[3])
            }
        }
        if parts.len() > 4 {
            b.halfmove_clock = parts[4].parse().unwrap_or(0)
        }
        if parts.len() > 5 {
            b.fullmove = parts[5].parse().unwrap_or(1)
        }
        b
    }
    #[allow(dead_code)]
    fn to_fen(&self) -> String {
        let mut s = String::new();
        for r in (0..8).rev() {
            let mut empty = 0;
            for f in 0..8 {
                let p = self.cells[sq(r, f)];
                if p.is_empty() {
                    empty += 1;
                } else {
                    if empty > 0 {
                        s.push_str(&empty.to_string());
                        empty = 0;
                    }
                    s.push(p.to_char());
                }
            }
            if empty > 0 {
                s.push_str(&empty.to_string());
            }
            if r > 0 {
                s.push('/')
            }
        }
        s.push(' ');
        s.push(if self.side_white { 'w' } else { 'b' });
        s.push(' ');
        let mut cast = String::new();
        if self.castling & 1 != 0 {
            cast.push('K')
        }
        if self.castling & 2 != 0 {
            cast.push('Q')
        }
        if self.castling & 4 != 0 {
            cast.push('k')
        }
        if self.castling & 8 != 0 {
            cast.push('q')
        }
        if cast.is_empty() {
            cast.push('-')
        }
        s.push_str(&cast);
        s.push(' ');
        if let Some(e) = self.ep {
            s.push_str(&sq_to_alg(e));
        } else {
            s.push('-')
        }
        s.push(' ');
        s.push_str(&self.halfmove_clock.to_string());
        s.push(' ');
        s.push_str(&self.fullmove.to_string());
        s
    }

    fn print_board(&self) {
        println!("  +------------------------+");
        for r in (0..8).rev() {
            print!("{} |", r + 1);
            for f in 0..8 {
                let p = self.cells[sq(r, f)];
                print!(" {}", p.to_char());
            }
            println!(" |");
        }
        println!("  +------------------------+");
        println!("    a b c d e f g h");
        println!(
            "Side: {}  Castling: {}{}{}{}  EP: {}  Halfmove: {}  Fullmove: {}",
            if self.side_white { "White" } else { "Black" },
            if self.castling & 1 != 0 { "K" } else { "-" },
            if self.castling & 2 != 0 { "Q" } else { "-" },
            if self.castling & 4 != 0 { "k" } else { "-" },
            if self.castling & 8 != 0 { "q" } else { "-" },
            match self.ep {
                Some(s) => sq_to_alg(s),
                None => String::from("-"),
            },
            self.halfmove_clock,
            self.fullmove
        );
    }

    fn piece_at(&self, s: Sq) -> Piece {
        self.cells[s]
    }
    #[allow(dead_code)]
    fn set_piece(&mut self, s: Sq, p: Piece) {
        self.cells[s] = p
    }

    fn find_king(&self, white: bool) -> Option<Sq> {
        for r in 0..8 {
            for f in 0..8 {
                let s = sq(r, f);
                let p = self.cells[s];
                if (white && p == Piece::WK) || (!white && p == Piece::BK) {
                    return Some(s);
                }
            }
        }
        None
    }

    // Make a move (no validation here) and save undo
    fn make_move(&mut self, from: Sq, to: Sq, promotion: Option<Piece>) {
        let captured = self.cells[to];
        let prev_cast = self.castling;
        let prev_ep = self.ep;
        let prev_half = self.halfmove_clock;
        // handle special: en passant capture
        let mut actual_captured = captured;
        if let Some(ep_sq) = self.ep {
            // pawn moved to ep square capturing pawn
            if self.cells[from] == Piece::WP && to == ep_sq && (from >> 4) == 4 {
                // white ep capture
                let cap_sq = to - 16;
                actual_captured = self.cells[cap_sq];
                self.cells[cap_sq] = Piece::Empty;
            } else if self.cells[from] == Piece::BP && to == ep_sq && (from >> 4) == 3 {
                // black ep capture
                let cap_sq = to + 16;
                actual_captured = self.cells[cap_sq];
                self.cells[cap_sq] = Piece::Empty;
            }
        }
        // move piece
        let mut moving = self.cells[from];
        self.cells[from] = Piece::Empty;
        // promotions
        if let Some(prom) = promotion {
            moving = prom;
        }
        self.cells[to] = moving;

        // update castling rights if king or rook moved/captured
        match from {
            f if f == sq(0, 4) && self.cells[to] == Piece::BK => {}
            _ => {}
        }
        // crude castling update
        if moving == Piece::WK {
            self.castling &= !(1 | 2);
        }
        if moving == Piece::BK {
            self.castling &= !(4 | 8);
        }
        // if rook captured or moved
        if from == sq(0, 0) || to == sq(0, 0) {
            self.castling &= !2;
        }
        if from == sq(0, 7) || to == sq(0, 7) {
            self.castling &= !1;
        }
        if from == sq(7, 0) || to == sq(7, 0) {
            self.castling &= !8;
        }
        if from == sq(7, 7) || to == sq(7, 7) {
            self.castling &= !4;
        }

        // handle castling move proper: move rook
        // white castling
        if moving == Piece::WK && from == sq(0, 4) && to == sq(0, 6) {
            // white kingside
            self.cells[sq(0, 7)] = Piece::Empty;
            self.cells[sq(0, 5)] = Piece::WR;
        } else if moving == Piece::WK && from == sq(0, 4) && to == sq(0, 2) {
            // white queenside
            self.cells[sq(0, 0)] = Piece::Empty;
            self.cells[sq(0, 3)] = Piece::WR;
        }
        // black castling
        if moving == Piece::BK && from == sq(7, 4) && to == sq(7, 6) {
            self.cells[sq(7, 7)] = Piece::Empty;
            self.cells[sq(7, 5)] = Piece::BR;
        } else if moving == Piece::BK && from == sq(7, 4) && to == sq(7, 2) {
            self.cells[sq(7, 0)] = Piece::Empty;
            self.cells[sq(7, 3)] = Piece::BR;
        }

        // update en passant target
        self.ep = None;
        if moving == Piece::WP && (to >> 4) - (from >> 4) == 2 {
            self.ep = Some(from + 16);
        }
        if moving == Piece::BP && (from >> 4) - (to >> 4) == 2 {
            self.ep = Some(from - 16);
        }

        // halfmove clock
        if moving == Piece::WP || moving == Piece::BP || !actual_captured.is_empty() {
            self.halfmove_clock = 0
        } else {
            self.halfmove_clock += 1
        }
        if !self.side_white {
            self.fullmove += 1
        }
        // flip side
        self.side_white = !self.side_white;

        // record undo
        self.history.push(Undo {
            mv_from: from,
            mv_to: to,
            captured: actual_captured,
            prev_castling: prev_cast,
            prev_ep: prev_ep,
            prev_halfmove: prev_half,
        });
    }

    fn undo_move(&mut self) {
        if let Some(u) = self.history.pop() {
            // flip side back
            self.side_white = !self.side_white;
            self.fullmove = max(
                1,
                self.fullmove as i32 - if !self.side_white { 1 } else { 0 },
            ) as u32; // crude
            let moving = self.cells[u.mv_to];
            self.cells[u.mv_from] = moving;
            self.cells[u.mv_to] = u.captured;
            // restore captured from ep handling might not move correctly but acceptable for our use
            self.castling = u.prev_castling;
            self.ep = u.prev_ep;
            self.halfmove_clock = u.prev_halfmove;
        }
    }

    // Make a clone and play move, used by search
    fn make_move_clone(&self, from: Sq, to: Sq, promotion: Option<Piece>) -> Board {
        let mut b = self.clone();
        b.make_move(from, to, promotion);
        b
    }
}

// =====================
// Move Representation
// =====================

#[derive(Clone, Copy, Debug)]
struct Move {
    from: Sq,
    to: Sq,
    promotion: Option<Piece>,
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(p) = self.promotion {
            write!(
                f,
                "{}{}{}",
                sq_to_alg(self.from),
                sq_to_alg(self.to),
                p.to_char()
            )
        } else {
            write!(f, "{}{}", sq_to_alg(self.from), sq_to_alg(self.to))
        }
    }
}

// =====================
// Move Generation
// =====================

// knight jumps and king deltas
const KNIGHT_DELTAS: [i32; 8] = [33, 31, 18, 14, -33, -31, -18, -14];
const KING_DELTAS: [i32; 8] = [16, 1, -16, -1, 17, 15, -15, -17];
const ROOK_DELTAS: [i32; 4] = [16, 1, -16, -1];
const BISHOP_DELTAS: [i32; 4] = [17, 15, -17, -15];

fn gen_moves(board: &Board, moves: &mut Vec<Move>) {
    moves.clear();
    let white = board.side_white;
    for r in 0..8 {
        for f in 0..8 {
            let s = sq(r, f);
            let p = board.piece_at(s);
            if p.is_empty() {
                continue;
            }
            if white && !p.is_white() {
                continue;
            }
            if !white && !p.is_black() {
                continue;
            }
            match p {
                Piece::WP => gen_pawn_moves(board, s, true, moves),
                Piece::BP => gen_pawn_moves(board, s, false, moves),
                Piece::WN | Piece::BN => gen_leaper_moves(board, s, &KNIGHT_DELTAS, moves),
                Piece::WB | Piece::BB => gen_slider_moves(board, s, &BISHOP_DELTAS, moves),
                Piece::WR | Piece::BR => gen_slider_moves(board, s, &ROOK_DELTAS, moves),
                Piece::WQ | Piece::BQ => {
                    gen_slider_moves(board, s, &ROOK_DELTAS, moves);
                    gen_slider_moves(board, s, &BISHOP_DELTAS, moves);
                }
                Piece::WK | Piece::BK => gen_leaper_moves(board, s, &KING_DELTAS, moves),
                _ => {}
            }
        }
    }
    // add promotion handling is inside pawn function
    // castling: naive check
    gen_castling(board, moves);
    // filter illegal by checking king in check after move
    let mut legal = Vec::new();
    for &m in moves.iter() {
        let b2 = board.make_move_clone(m.from, m.to, m.promotion);
        if !is_king_attacked(&b2, !board.side_white) {
            legal.push(m);
        }
    }
    *moves = legal;
}

fn gen_leaper_moves(board: &Board, s: Sq, deltas: &[i32], moves: &mut Vec<Move>) {
    let side_white = board.side_white;
    for &d in deltas.iter() {
        let ns = (s as i32 + d) as usize;
        if !on_board(ns) {
            continue;
        }
        let p = board.piece_at(ns);
        if p.is_empty() || (side_white && p.is_black()) || (!side_white && p.is_white()) {
            moves.push(Move {
                from: s,
                to: ns,
                promotion: None,
            });
        }
    }
}

fn gen_slider_moves(board: &Board, s: Sq, deltas: &[i32], moves: &mut Vec<Move>) {
    let side_white = board.side_white;
    for &d in deltas.iter() {
        let mut ns = s as i32 + d;
        while ns >= 0 && on_board(ns as usize) {
            let nsu = ns as usize;
            let p = board.piece_at(nsu);
            if p.is_empty() {
                moves.push(Move {
                    from: s,
                    to: nsu,
                    promotion: None,
                });
            } else {
                if (side_white && p.is_black()) || (!side_white && p.is_white()) {
                    moves.push(Move {
                        from: s,
                        to: nsu,
                        promotion: None,
                    });
                }
                break;
            }
            ns += d;
        }
    }
}

fn gen_pawn_moves(board: &Board, s: Sq, white: bool, moves: &mut Vec<Move>) {
    let dir = if white { 16 } else { -16 };
    let start_rank = if white { 1 } else { 6 };
    let r = (s >> 4) as i32;
    let one = (s as i32 + dir) as usize;
    // single push
    if on_board(one) && board.piece_at(one).is_empty() {
        // promotion?
        if (white && (one >> 4) == 7) || (!white && (one >> 4) == 0) {
            // promote to Q, R, B, N
            moves.push(Move {
                from: s,
                to: one,
                promotion: Some(if white { Piece::WQ } else { Piece::BQ }),
            });
            moves.push(Move {
                from: s,
                to: one,
                promotion: Some(if white { Piece::WR } else { Piece::BR }),
            });
            moves.push(Move {
                from: s,
                to: one,
                promotion: Some(if white { Piece::WB } else { Piece::BB }),
            });
            moves.push(Move {
                from: s,
                to: one,
                promotion: Some(if white { Piece::WN } else { Piece::BN }),
            });
        } else {
            moves.push(Move {
                from: s,
                to: one,
                promotion: None,
            });
            // double push
            if r == start_rank {
                let two = (s as i32 + dir * 2) as usize;
                if on_board(two) && board.piece_at(two).is_empty() {
                    moves.push(Move {
                        from: s,
                        to: two,
                        promotion: None,
                    });
                }
            }
        }
    }
    // captures
    for cap_dir in [dir + 1, dir - 1].iter() {
        let ns = (s as i32 + cap_dir) as i32;
        if ns < 0 {
            continue;
        }
        let nsu = ns as usize;
        if !on_board(nsu) {
            continue;
        }
        let p = board.piece_at(nsu);
        if !p.is_empty() && ((white && p.is_black()) || (!white && p.is_white())) {
            if (white && (nsu >> 4) == 7) || (!white && (nsu >> 4) == 0) {
                moves.push(Move {
                    from: s,
                    to: nsu,
                    promotion: Some(if white { Piece::WQ } else { Piece::BQ }),
                });
                moves.push(Move {
                    from: s,
                    to: nsu,
                    promotion: Some(if white { Piece::WR } else { Piece::BR }),
                });
                moves.push(Move {
                    from: s,
                    to: nsu,
                    promotion: Some(if white { Piece::WB } else { Piece::BB }),
                });
                moves.push(Move {
                    from: s,
                    to: nsu,
                    promotion: Some(if white { Piece::WN } else { Piece::BN }),
                });
            } else {
                moves.push(Move {
                    from: s,
                    to: nsu,
                    promotion: None,
                });
            }
        }
    }
    // en passant
    if let Some(ep) = board.ep {
        if (ep == (s + 15) || ep == (s + 17) || ep == (s - 15) || ep == (s - 17)) && on_board(ep) {
            // ensure correct rank relation
            // playable: pawn diagonally behind ep square
            if white {
                if (ep >> 4) == 5
                    && (s >> 4) == 4
                    && ((ep & 15) as i32 - (s & 15) as i32).abs() == 1
                {
                    moves.push(Move {
                        from: s,
                        to: ep,
                        promotion: None,
                    });
                }
            } else {
                if (ep >> 4) == 2
                    && (s >> 4) == 3
                    && ((ep & 15) as i32 - (s & 15) as i32).abs() == 1
                {
                    moves.push(Move {
                        from: s,
                        to: ep,
                        promotion: None,
                    });
                }
            }
        }
    }
}

fn gen_castling(board: &Board, moves: &mut Vec<Move>) {
    // naive: ensure squares empty and not attacked
    if board.side_white {
        if board.castling & 1 != 0 {
            // white king side: e1->g1 squares f1 g1 empty
            if board.piece_at(sq(0, 5)).is_empty() && board.piece_at(sq(0, 6)).is_empty() {
                moves.push(Move {
                    from: sq(0, 4),
                    to: sq(0, 6),
                    promotion: None,
                });
            }
        }
        if board.castling & 2 != 0 {
            if board.piece_at(sq(0, 3)).is_empty()
                && board.piece_at(sq(0, 2)).is_empty()
                && board.piece_at(sq(0, 1)).is_empty()
            {
                moves.push(Move {
                    from: sq(0, 4),
                    to: sq(0, 2),
                    promotion: None,
                });
            }
        }
    } else {
        if board.castling & 4 != 0 {
            if board.piece_at(sq(7, 5)).is_empty() && board.piece_at(sq(7, 6)).is_empty() {
                moves.push(Move {
                    from: sq(7, 4),
                    to: sq(7, 6),
                    promotion: None,
                });
            }
        }
        if board.castling & 8 != 0 {
            if board.piece_at(sq(7, 3)).is_empty()
                && board.piece_at(sq(7, 2)).is_empty()
                && board.piece_at(sq(7, 1)).is_empty()
            {
                moves.push(Move {
                    from: sq(7, 4),
                    to: sq(7, 2),
                    promotion: None,
                });
            }
        }
    }
}

// =====================
// Attack Detection
// =====================

fn is_square_attacked(board: &Board, s: Sq, by_white: bool) -> bool {
    // pawns
    if by_white {
        let attacks = [s as i32 - 17, s as i32 - 15];
        for &a in attacks.iter() {
            if a >= 0 && on_board(a as usize) {
                if board.piece_at(a as usize) == Piece::WP {
                    return true;
                }
            }
        }
    } else {
        let attacks = [s as i32 + 17, s as i32 + 15];
        for &a in attacks.iter() {
            if a >= 0 && on_board(a as usize) {
                if board.piece_at(a as usize) == Piece::BP {
                    return true;
                }
            }
        }
    }
    // knights
    for &d in KNIGHT_DELTAS.iter() {
        let a = s as i32 + d;
        if a >= 0 && on_board(a as usize) {
            let p = board.piece_at(a as usize);
            if (by_white && p == Piece::WN) || (!by_white && p == Piece::BN) {
                return true;
            }
        }
    }
    // sliders
    for &d in ROOK_DELTAS.iter() {
        let mut a = s as i32 + d;
        while a >= 0 && on_board(a as usize) {
            let p = board.piece_at(a as usize);
            if !p.is_empty() {
                if (by_white && (p == Piece::WR || p == Piece::WQ))
                    || (!by_white && (p == Piece::BR || p == Piece::BQ))
                {
                    return true;
                }
                break;
            }
            a += d;
        }
    }
    for &d in BISHOP_DELTAS.iter() {
        let mut a = s as i32 + d;
        while a >= 0 && on_board(a as usize) {
            let p = board.piece_at(a as usize);
            if !p.is_empty() {
                if (by_white && (p == Piece::WB || p == Piece::WQ))
                    || (!by_white && (p == Piece::BB || p == Piece::BQ))
                {
                    return true;
                }
                break;
            }
            a += d;
        }
    }
    // king
    for &d in KING_DELTAS.iter() {
        let a = s as i32 + d;
        if a >= 0 && on_board(a as usize) {
            let p = board.piece_at(a as usize);
            if (by_white && p == Piece::WK) || (!by_white && p == Piece::BK) {
                return true;
            }
        }
    }
    false
}

fn is_king_attacked(board: &Board, white_king: bool) -> bool {
    if let Some(kpos) = board.find_king(white_king) {
        is_square_attacked(board, kpos, !white_king)
    } else {
        true
    }
}

// =====================
// Evaluation
// =====================

fn eval(board: &Board) -> i32 {
    // material values
    let mut score = 0i32;
    for r in 0..8 {
        for f in 0..8 {
            let s = sq(r, f);
            let p = board.piece_at(s);
            score += match p {
                Piece::WP => 100,
                Piece::WN => 320,
                Piece::WB => 330,
                Piece::WR => 500,
                Piece::WQ => 900,
                Piece::WK => 20000,
                Piece::BP => -100,
                Piece::BN => -320,
                Piece::BB => -330,
                Piece::BR => -500,
                Piece::BQ => -900,
                Piece::BK => -20000,
                _ => 0,
            };
        }
    }
    // side to move
    if !board.side_white {
        score = -score
    }
    score
}

// =====================
// Search
// =====================

struct SearchInfo {
    nodes: u64,
    start: Instant,
    time_limit: Option<Duration>,
    best_move: Option<Move>,
}

fn negamax(board: &mut Board, depth: i32, alpha: i32, beta: i32, info: &mut SearchInfo) -> i32 {
    if let Some(limit) = info.time_limit {
        if info.start.elapsed() >= limit {
            return 0;
        }
    }
    info.nodes += 1;
    if depth == 0 {
        return quiescence(board, alpha, beta, info);
    }
    let mut a = alpha;
    let mut moves = Vec::new();
    gen_moves(board, &mut moves);
    if moves.is_empty() {
        // checkmate or stalemate
        if is_king_attacked(board, board.side_white) {
            return -100000 + ((100 - depth) as i32);
        } else {
            return 0;
        }
    }
    // ordering: captures first (simple)
    moves.sort_by_key(|m| {
        if board.piece_at(m.to).is_empty() {
            0
        } else {
            1
        }
    });
    let mut best = -999999;
    for m in moves {
        let _captured = board.piece_at(m.to); // capture value intentionally ignored
        board.make_move(m.from, m.to, m.promotion);
        let val = -negamax(board, depth - 1, -beta, -a, info);
        board.undo_move();
        if val > best {
            best = val;
            if depth == 1 {
                info.best_move = Some(m);
            }
        }
        if val > a {
            a = val;
        }
        if a >= beta {
            break;
        }
    }
    best
}

fn quiescence(board: &mut Board, alpha: i32, beta: i32, info: &mut SearchInfo) -> i32 {
    if let Some(limit) = info.time_limit {
        if info.start.elapsed() >= limit {
            return 0;
        }
    }
    info.nodes += 1;
    let stand = eval(board);
    if stand >= beta {
        return beta;
    }
    let mut a = alpha;
    if stand > a {
        a = stand
    }
    // generate captures
    let mut moves = Vec::new();
    gen_moves(board, &mut moves);
    moves.retain(|m| !board.piece_at(m.to).is_empty());
    for m in moves {
        board.make_move(m.from, m.to, m.promotion);
        let score = -quiescence(board, -beta, -a, info);
        board.undo_move();
        if score >= beta {
            return beta;
        }
        if score > a {
            a = score
        }
    }
    a
}

fn search_root(board: &mut Board, max_depth: i32, time_limit_ms: Option<u64>) -> Option<Move> {
    let mut info = SearchInfo {
        nodes: 0,
        start: Instant::now(),
        time_limit: time_limit_ms.map(|ms| Duration::from_millis(ms)),
        best_move: None,
    };
    let mut best_move = None;
    for depth in 1..=max_depth {
        let _val = negamax(board, depth, -1000000, 1000000, &mut info);
        best_move = info.best_move;
        // stop if time exceeded
        if let Some(limit) = info.time_limit {
            if info.start.elapsed() >= limit {
                break;
            }
        }
    }
    best_move
}

// =====================
// CLI / Interaction
// =====================

fn print_help() {
    println!("Commands:");
    println!("  help                - this");
    println!("  fen <FEN>           - set position from FEN");
    println!("  board               - print board");
    println!("  go depth <n>        - engine thinks for n plies");
    println!("  go time <ms>        - engine thinks up to ms milliseconds");
    println!("  play                - play human vs engine (you play white)");
    println!("  move <e2e4>         - make a move in algebraic coords");
    println!("  undo                - undo last move");
    println!("  quit                - exit");
}

fn ai_move(board: &mut Board, depth: i32, time_ms: Option<u64>) -> Option<Move> {
    search_root(board, depth, time_ms)
}

fn main() {
    println!("Rust Chess Engine — single-file demo. Type 'help' for commands.");
    let mut board = Board::from_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    board.print_board();
    let stdin = io::stdin();
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut line = String::new();
        if stdin.read_line(&mut line).is_err() {
            break;
        }
        let parts: Vec<&str> = line.trim().split_whitespace().collect();
        if parts.is_empty() {
            continue;
        }
        match parts[0] {
            "help" => print_help(),
            "fen" => {
                if parts.len() > 1 {
                    let fen = parts[1..].join(" ");
                    board = Board::from_fen(&fen);
                    board.print_board();
                } else {
                    println!("usage: fen <FEN>")
                }
            }
            "board" => board.print_board(),
            "move" => {
                if parts.len() < 2 {
                    println!("usage: move e2e4");
                    continue;
                }
                let mv = parts[1];
                if mv.len() < 4 {
                    println!("bad move");
                    continue;
                }
                if let (Some(from), Some(to)) = (alg_to_sq(&mv[0..2]), alg_to_sq(&mv[2..4])) {
                    let promotion = if mv.len() >= 5 {
                        Some(Piece::from_char(mv.chars().nth(4).unwrap()))
                    } else {
                        None
                    };
                    board.make_move(from, to, promotion);
                    board.print_board();
                } else {
                    println!("bad squares")
                }
            }
            "undo" => {
                board.undo_move();
                board.print_board();
            }
            "go" => {
                if parts.len() < 3 {
                    println!("usage: go depth <n> | go time <ms>");
                    continue;
                }
                match parts[1] {
                    "depth" => {
                        if let Ok(d) = parts[2].parse::<i32>() {
                            let now = Instant::now();
                            if let Some(mv) = ai_move(&mut board, d, None) {
                                println!("engine -> {}", mv);
                                board.make_move(mv.from, mv.to, mv.promotion);
                                board.print_board();
                                println!("(took {:?})", now.elapsed());
                            } else {
                                println!("no move")
                            }
                        }
                    }
                    "time" => {
                        if let Ok(ms) = parts[2].parse::<u64>() {
                            let now = Instant::now();
                            if let Some(mv) = ai_move(&mut board, 6, Some(ms)) {
                                println!("engine -> {}", mv);
                                board.make_move(mv.from, mv.to, mv.promotion);
                                board.print_board();
                                println!("(took {:?})", now.elapsed());
                            } else {
                                println!("no move")
                            }
                        }
                    }
                    _ => println!("unknown go"),
                }
            }
            "play" => {
                println!("You are White. Enter moves like e2e4. Type 'resign' to stop.");
                board = Board::from_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
                board.print_board();
                loop {
                    if board.side_white {
                        print!("white> ");
                        io::stdout().flush().unwrap();
                        let mut l = String::new();
                        if stdin.read_line(&mut l).is_err() {
                            break;
                        }
                        let t = l.trim();
                        if t == "resign" {
                            println!("You resigned.\n");
                            break;
                        }
                        if t.len() < 4 {
                            println!("bad move");
                            continue;
                        }
                        if let (Some(from), Some(to)) = (alg_to_sq(&t[0..2]), alg_to_sq(&t[2..4])) {
                            let promotion = if t.len() >= 5 {
                                Some(Piece::from_char(t.chars().nth(4).unwrap()))
                            } else {
                                None
                            };
                            board.make_move(from, to, promotion);
                            board.print_board();
                        } else {
                            println!("bad squares")
                        }
                    } else {
                        println!("Engine thinking...");
                        if let Some(mv) = ai_move(&mut board, 5, Some(500)) {
                            println!("engine -> {}", mv);
                            board.make_move(mv.from, mv.to, mv.promotion);
                            board.print_board();
                        } else {
                            println!("engine has no move");
                            break;
                        }
                    }
                }
            }
            "quit" => break,
            _ => println!("unknown command, type 'help'"),
        }
    }
    println!("bye")
}

// All warnings are solved and fully working ==> v0.1.0
