"""
Chess Game in Python - Tkinter GUI with 3 AI difficulty levels
  Easy   → random legal moves
  Medium → 1-ply minimax with basic piece values
  Hard   → 3-ply minimax with alpha-beta pruning + positional tables
"""

import tkinter as tk
from tkinter import messagebox, ttk
import random
import copy
import threading

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────
LIGHT = "#F0D9B5"
DARK  = "#B58863"
HIGH  = "#ACEA6A"   # selected / valid move highlight
LAST  = "#CDD16E"   # last move highlight
CHECK = "#FF6B6B"   # king in check

PIECE_UNICODE = {
    'K': '♔', 'Q': '♕', 'R': '♖', 'B': '♗', 'N': '♘', 'P': '♙',
    'k': '♚', 'q': '♛', 'r': '♜', 'b': '♝', 'n': '♞', 'p': '♟',
}

PIECE_VALUES = {'P': 100, 'N': 320, 'B': 330, 'R': 500, 'Q': 900, 'K': 20000,
                'p': -100, 'n': -320, 'b': -330, 'r': -500, 'q': -900, 'k': -20000}

# Positional bonus tables (white perspective; mirrored for black)
PAWN_TABLE = [
     0,  0,  0,  0,  0,  0,  0,  0,
    50, 50, 50, 50, 50, 50, 50, 50,
    10, 10, 20, 30, 30, 20, 10, 10,
     5,  5, 10, 25, 25, 10,  5,  5,
     0,  0,  0, 20, 20,  0,  0,  0,
     5, -5,-10,  0,  0,-10, -5,  5,
     5, 10, 10,-20,-20, 10, 10,  5,
     0,  0,  0,  0,  0,  0,  0,  0,
]
KNIGHT_TABLE = [
    -50,-40,-30,-30,-30,-30,-40,-50,
    -40,-20,  0,  0,  0,  0,-20,-40,
    -30,  0, 10, 15, 15, 10,  0,-30,
    -30,  5, 15, 20, 20, 15,  5,-30,
    -30,  0, 15, 20, 20, 15,  0,-30,
    -30,  5, 10, 15, 15, 10,  5,-30,
    -40,-20,  0,  5,  5,  0,-20,-40,
    -50,-40,-30,-30,-30,-30,-40,-50,
]
BISHOP_TABLE = [
    -20,-10,-10,-10,-10,-10,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5, 10, 10,  5,  0,-10,
    -10,  5,  5, 10, 10,  5,  5,-10,
    -10,  0, 10, 10, 10, 10,  0,-10,
    -10, 10, 10, 10, 10, 10, 10,-10,
    -10,  5,  0,  0,  0,  0,  5,-10,
    -20,-10,-10,-10,-10,-10,-10,-20,
]
ROOK_TABLE = [
     0,  0,  0,  0,  0,  0,  0,  0,
     5, 10, 10, 10, 10, 10, 10,  5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
     0,  0,  0,  5,  5,  0,  0,  0,
]
QUEEN_TABLE = [
    -20,-10,-10, -5, -5,-10,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5,  5,  5,  5,  0,-10,
     -5,  0,  5,  5,  5,  5,  0, -5,
      0,  0,  5,  5,  5,  5,  0, -5,
    -10,  5,  5,  5,  5,  5,  0,-10,
    -10,  0,  5,  0,  0,  0,  0,-10,
    -20,-10,-10, -5, -5,-10,-10,-20,
]
KING_TABLE = [
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -20,-30,-30,-40,-40,-30,-30,-20,
    -10,-20,-20,-20,-20,-20,-20,-10,
     20, 20,  0,  0,  0,  0, 20, 20,
     20, 30, 10,  0,  0, 10, 30, 20,
]

POS_TABLES = {
    'P': PAWN_TABLE, 'N': KNIGHT_TABLE, 'B': BISHOP_TABLE,
    'R': ROOK_TABLE, 'Q': QUEEN_TABLE,  'K': KING_TABLE,
}


# ─────────────────────────────────────────────────────────────────────────────
# CHESS LOGIC
# ─────────────────────────────────────────────────────────────────────────────
class ChessBoard:
    def __init__(self):
        self.reset()

    def reset(self):
        self.board = [
            ['r','n','b','q','k','b','n','r'],
            ['p','p','p','p','p','p','p','p'],
            [None]*8, [None]*8, [None]*8, [None]*8,
            ['P','P','P','P','P','P','P','P'],
            ['R','N','B','Q','K','B','N','R'],
        ]
        self.turn = 'white'
        self.castling = {'K': True, 'Q': True, 'k': True, 'q': True}
        self.en_passant = None      # target square (row, col) if available
        self.move_history = []
        self.captured = {'white': [], 'black': []}
        self.halfmove_clock = 0
        self.fullmove_number = 1

    # ── helpers ──────────────────────────────────────────────────────────────
    @staticmethod
    def is_white(p): return p is not None and p.isupper()
    @staticmethod
    def is_black(p): return p is not None and p.islower()
    @staticmethod
    def color(p):
        if p is None: return None
        return 'white' if p.isupper() else 'black'

    def enemy(self, color): return 'black' if color == 'white' else 'white'

    def piece_at(self, r, c):
        if 0 <= r < 8 and 0 <= c < 8:
            return self.board[r][c]
        return None

    def find_king(self, color):
        k = 'K' if color == 'white' else 'k'
        for r in range(8):
            for c in range(8):
                if self.board[r][c] == k:
                    return r, c
        return None

    # ── raw move generation (does NOT check legality re: own-king safety) ──
    def pseudo_moves(self, r, c, board=None):
        if board is None: board = self.board
        piece = board[r][c]
        if piece is None: return []
        color = 'white' if piece.isupper() else 'black'
        moves = []
        p = piece.upper()

        def add(nr, nc, flag=None):
            if 0 <= nr < 8 and 0 <= nc < 8:
                target = board[nr][nc]
                if target is None or self.color(target) != color:
                    moves.append((nr, nc, flag))

        def slide(dr, dc):
            nr, nc = r+dr, c+dc
            while 0 <= nr < 8 and 0 <= nc < 8:
                target = board[nr][nc]
                if target is None:
                    moves.append((nr, nc, None))
                elif self.color(target) != color:
                    moves.append((nr, nc, None)); break
                else:
                    break
                nr += dr; nc += dc

        if p == 'P':
            d = -1 if color == 'white' else 1
            start_row = 6 if color == 'white' else 1
            # forward
            if 0 <= r+d < 8 and board[r+d][c] is None:
                moves.append((r+d, c, 'promo' if r+d in (0,7) else None))
                if r == start_row and board[r+2*d][c] is None:
                    moves.append((r+2*d, c, 'double'))
            # captures
            for dc in (-1, 1):
                nr, nc = r+d, c+dc
                if 0 <= nr < 8 and 0 <= nc < 8:
                    target = board[nr][nc]
                    if target is not None and self.color(target) != color:
                        moves.append((nr, nc, 'promo' if nr in (0,7) else None))
                    elif (nr, nc) == self.en_passant:
                        moves.append((nr, nc, 'ep'))
        elif p == 'N':
            for dr, dc in [(-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)]:
                add(r+dr, c+dc)
        elif p == 'B':
            for dr, dc in [(-1,-1),(-1,1),(1,-1),(1,1)]: slide(dr, dc)
        elif p == 'R':
            for dr, dc in [(-1,0),(1,0),(0,-1),(0,1)]: slide(dr, dc)
        elif p == 'Q':
            for dr, dc in [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]: slide(dr, dc)
        elif p == 'K':
            for dr, dc in [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]: add(r+dr, c+dc)
            # castling (kingside)
            row = 7 if color == 'white' else 0
            if r == row and c == 4:
                if color == 'white' and self.castling['K']:
                    if board[row][5] is None and board[row][6] is None:
                        moves.append((row, 6, 'castle_k'))
                if color == 'white' and self.castling['Q']:
                    if board[row][3] is None and board[row][2] is None and board[row][1] is None:
                        moves.append((row, 2, 'castle_q'))
                if color == 'black' and self.castling['k']:
                    if board[row][5] is None and board[row][6] is None:
                        moves.append((row, 6, 'castle_k'))
                if color == 'black' and self.castling['q']:
                    if board[row][3] is None and board[row][2] is None and board[row][1] is None:
                        moves.append((row, 2, 'castle_q'))
        return moves

    def is_square_attacked(self, r, c, by_color, board=None):
        if board is None: board = self.board
        for rr in range(8):
            for cc in range(8):
                p = board[rr][cc]
                if p is not None and self.color(p) == by_color:
                    for nr, nc, _ in self.pseudo_moves(rr, cc, board):
                        if nr == r and nc == c:
                            return True
        return False

    def in_check(self, color, board=None):
        if board is None: board = self.board
        kr, kc = self.find_king_b(color, board)
        if kr is None: return False
        return self.is_square_attacked(kr, kc, self.enemy(color), board)

    def find_king_b(self, color, board):
        k = 'K' if color == 'white' else 'k'
        for r in range(8):
            for c in range(8):
                if board[r][c] == k:
                    return r, c
        return None, None

    def apply_move_to_board(self, board, r, c, nr, nc, flag, promo='Q'):
        """Returns new board state (list of lists) after applying move."""
        b = [row[:] for row in board]
        piece = b[r][c]
        color = 'white' if piece.isupper() else 'black'

        b[nr][nc] = piece
        b[r][c] = None

        if flag == 'promo':
            b[nr][nc] = promo if color == 'white' else promo.lower()
        elif flag == 'ep':
            ep_r = nr + (1 if color == 'white' else -1)
            b[ep_r][nc] = None
        elif flag in ('castle_k', 'castle_q'):
            row = r
            if flag == 'castle_k':
                b[row][5] = b[row][7]; b[row][7] = None
            else:
                b[row][3] = b[row][0]; b[row][0] = None
        return b

    def legal_moves(self, color=None, board=None):
        if color is None: color = self.turn
        if board is None: board = self.board
        result = []
        for r in range(8):
            for c in range(8):
                p = board[r][c]
                if p is None or self.color(p) != color: continue
                for nr, nc, flag in self.pseudo_moves(r, c, board):
                    # For castling, also check intermediate squares
                    if flag == 'castle_k':
                        if self.in_check(color, board): continue
                        mid_b = self.apply_move_to_board(board, r, c, r, c+1, None)
                        if self.in_check(color, mid_b): continue
                    elif flag == 'castle_q':
                        if self.in_check(color, board): continue
                        mid_b = self.apply_move_to_board(board, r, c, r, c-1, None)
                        if self.in_check(color, mid_b): continue
                    nb = self.apply_move_to_board(board, r, c, nr, nc, flag)
                    if not self.in_check(color, nb):
                        result.append((r, c, nr, nc, flag))
        return result

    def make_move(self, r, c, nr, nc, flag, promo='Q'):
        piece = self.board[r][c]
        color = self.turn
        captured = self.board[nr][nc]

        # en passant capture
        if flag == 'ep':
            ep_r = nr + (1 if color == 'white' else -1)
            captured = self.board[ep_r][nc]
            self.board[ep_r][nc] = None

        self.board[nr][nc] = piece
        self.board[r][c] = None

        if captured:
            self.captured[color].append(captured)

        if flag == 'promo':
            self.board[nr][nc] = promo if color == 'white' else promo.lower()
        elif flag == 'castle_k':
            self.board[nr][5] = self.board[nr][7]; self.board[nr][7] = None
        elif flag == 'castle_q':
            self.board[nr][3] = self.board[nr][0]; self.board[nr][0] = None

        # update castling rights
        if piece == 'K': self.castling['K'] = self.castling['Q'] = False
        if piece == 'k': self.castling['k'] = self.castling['q'] = False
        if piece == 'R' and r == 7:
            if c == 7: self.castling['K'] = False
            if c == 0: self.castling['Q'] = False
        if piece == 'r' and r == 0:
            if c == 7: self.castling['k'] = False
            if c == 0: self.castling['q'] = False

        # en passant target
        self.en_passant = (nr + (1 if color=='white' else -1), nc) if flag == 'double' else None

        self.move_history.append((r, c, nr, nc, flag, piece, captured))
        self.turn = self.enemy(color)

        if color == 'black':
            self.fullmove_number += 1

    def game_status(self):
        """Returns: 'playing', 'checkmate_white', 'checkmate_black', 'stalemate', 'draw'"""
        moves = self.legal_moves(self.turn)
        if moves:
            # Fifty-move rule (simplified)
            if self.halfmove_clock >= 100:
                return 'draw'
            return 'playing'
        if self.in_check(self.turn):
            return f'checkmate_{self.enemy(self.turn)}'
        return 'stalemate'


# ─────────────────────────────────────────────────────────────────────────────
# AI ENGINE
# ─────────────────────────────────────────────────────────────────────────────
class ChessAI:
    def __init__(self, difficulty='medium'):
        self.difficulty = difficulty  # 'easy', 'medium', 'hard'

    def get_move(self, chess: ChessBoard):
        moves = chess.legal_moves('black')
        if not moves:
            return None
        if self.difficulty == 'easy':
            return self._random_move(moves)
        elif self.difficulty == 'medium':
            return self._minimax_move(chess, moves, depth=2)
        else:
            return self._minimax_move(chess, moves, depth=3)

    def _random_move(self, moves):
        return random.choice(moves)

    def _minimax_move(self, chess: ChessBoard, moves, depth):
        best_score = float('-inf')
        best_move = moves[0]
        alpha, beta = float('-inf'), float('inf')
        random.shuffle(moves)
        for move in moves:
            nb = chess.apply_move_to_board(chess.board, *move[:4], move[4])
            score = self._minimax(chess, nb, depth - 1, alpha, beta, True)
            if score > best_score:
                best_score = score
                best_move = move
            alpha = max(alpha, score)
        return best_move

    def _minimax(self, chess: ChessBoard, board, depth, alpha, beta, is_max):
        color = 'white' if is_max else 'black'
        moves = chess.legal_moves(color, board)

        if depth == 0 or not moves:
            return self._evaluate(chess, board)

        if is_max:
            best = float('-inf')
            for move in moves:
                nb = chess.apply_move_to_board(board, *move[:4], move[4])
                best = max(best, self._minimax(chess, nb, depth-1, alpha, beta, False))
                alpha = max(alpha, best)
                if beta <= alpha: break
            return best
        else:
            best = float('inf')
            for move in moves:
                nb = chess.apply_move_to_board(board, *move[:4], move[4])
                best = min(best, self._minimax(chess, nb, depth-1, alpha, beta, True))
                beta = min(beta, best)
                if beta <= alpha: break
            return best

    def _evaluate(self, chess: ChessBoard, board):
        score = 0
        for r in range(8):
            for c in range(8):
                p = board[r][c]
                if p is None: continue
                val = PIECE_VALUES.get(p, 0)
                # positional bonus
                pu = p.upper()
                if pu in POS_TABLES:
                    if chess.is_white(p):
                        pos = POS_TABLES[pu][r * 8 + c]
                    else:
                        pos = -POS_TABLES[pu][(7 - r) * 8 + c]
                else:
                    pos = 0
                score += val + pos
        return score


# ─────────────────────────────────────────────────────────────────────────────
# GUI
# ─────────────────────────────────────────────────────────────────────────────
CELL = 72   # pixels per square

class ChessApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("♟ Python Chess")
        self.resizable(False, False)
        self.configure(bg="#2c2c2c")

        self.chess = ChessBoard()
        self.ai = ChessAI('medium')
        self.selected = None
        self.valid_moves = []
        self.last_move = None
        self.ai_thinking = False
        self.player_color = 'white'   # player always plays white
        self.promotion_choice = 'Q'

        self._build_ui()
        self.draw_board()

    # ── UI layout ─────────────────────────────────────────────────────────
    def _build_ui(self):
        # top bar
        top = tk.Frame(self, bg="#2c2c2c")
        top.pack(fill='x', padx=10, pady=(10, 0))

        tk.Label(top, text="Difficulty:", bg="#2c2c2c", fg="white",
                 font=("Helvetica", 12)).pack(side='left')
        self.diff_var = tk.StringVar(value='Medium')
        diff_menu = ttk.Combobox(top, textvariable=self.diff_var,
                                 values=['Easy', 'Medium', 'Hard'],
                                 state='readonly', width=8, font=("Helvetica", 11))
        diff_menu.pack(side='left', padx=6)
        diff_menu.bind('<<ComboboxSelected>>', self._on_diff_change)

        tk.Button(top, text="New Game", command=self.new_game,
                  bg="#4CAF50", fg="white", font=("Helvetica", 11, "bold"),
                  relief='flat', padx=10, pady=3).pack(side='right')

        # main area
        main = tk.Frame(self, bg="#2c2c2c")
        main.pack(padx=10, pady=8)

        # rank labels left
        left_labels = tk.Frame(main, bg="#2c2c2c")
        left_labels.grid(row=0, column=0)
        for i, lbl in enumerate("87654321"):
            tk.Label(left_labels, text=lbl, bg="#2c2c2c", fg="#aaa",
                     font=("Helvetica", 10), width=2).grid(row=i)

        # canvas
        self.canvas = tk.Canvas(main, width=CELL*8, height=CELL*8,
                                 highlightthickness=2, highlightbackground="#888")
        self.canvas.grid(row=0, column=1)
        self.canvas.bind("<Button-1>", self._on_click)

        # file labels bottom
        bot_labels = tk.Frame(main, bg="#2c2c2c")
        bot_labels.grid(row=1, column=1)
        for lbl in "abcdefgh":
            tk.Label(bot_labels, text=lbl, bg="#2c2c2c", fg="#aaa",
                     font=("Helvetica", 10), width=int(CELL/9)+1).pack(side='left')

        # status / captured
        bottom = tk.Frame(self, bg="#2c2c2c")
        bottom.pack(fill='x', padx=10, pady=(0, 10))

        self.status_var = tk.StringVar(value="Your turn (White)")
        tk.Label(bottom, textvariable=self.status_var, bg="#2c2c2c", fg="#e0e0e0",
                 font=("Helvetica", 12, "bold")).pack(side='left')

        self.cap_var = tk.StringVar(value="")
        tk.Label(bottom, textvariable=self.cap_var, bg="#2c2c2c", fg="#aaa",
                 font=("Helvetica", 10)).pack(side='right')

    # ── drawing ───────────────────────────────────────────────────────────
    def draw_board(self):
        self.canvas.delete('all')
        in_check_sq = None
        if self.chess.in_check(self.chess.turn):
            in_check_sq = self.chess.find_king_b(self.chess.turn, self.chess.board)

        for r in range(8):
            for c in range(8):
                x1, y1 = c*CELL, r*CELL
                x2, y2 = x1+CELL, y1+CELL

                # base color
                base = LIGHT if (r+c) % 2 == 0 else DARK

                # override with highlight
                sq = (r, c)
                if self.last_move and sq in (self.last_move[:2], self.last_move[2:4]):
                    color = LAST
                elif in_check_sq and sq == in_check_sq:
                    color = CHECK
                elif self.selected and sq == self.selected:
                    color = HIGH
                elif sq in [(m[2], m[3]) for m in self.valid_moves]:
                    color = HIGH
                else:
                    color = base

                self.canvas.create_rectangle(x1, y1, x2, y2, fill=color, outline='')

                # dot for valid move (empty square)
                if sq in [(m[2], m[3]) for m in self.valid_moves]:
                    piece = self.chess.board[r][c]
                    if piece is None:
                        cx, cy = x1+CELL//2, y1+CELL//2
                        self.canvas.create_oval(cx-10, cy-10, cx+10, cy+10,
                                                fill="#44AA44", outline='')

                # piece
                piece = self.chess.board[r][c]
                if piece:
                    sym = PIECE_UNICODE.get(piece, piece)
                    self.canvas.create_text(x1+CELL//2, y1+CELL//2, text=sym,
                                            font=("Arial", int(CELL*0.62)),
                                            fill='white' if piece.isupper() else '#111')

        self._update_status()
        self._update_captured()

    def _update_status(self):
        status = self.chess.game_status()
        turn = self.chess.turn
        if status == 'playing':
            check = " ⚠ CHECK!" if self.chess.in_check(turn) else ""
            if turn == 'white':
                self.status_var.set(f"Your turn (White){check}")
            else:
                txt = "🤖 AI thinking..." if self.ai_thinking else f"AI's turn (Black){check}"
                self.status_var.set(txt)
        elif 'checkmate' in status:
            winner = 'White' if 'white' in status else 'Black'
            self.status_var.set(f"♛ Checkmate! {winner} wins!")
        elif status == 'stalemate':
            self.status_var.set("Stalemate – It's a draw!")
        elif status == 'draw':
            self.status_var.set("Draw by 50-move rule!")

    def _update_captured(self):
        w = ''.join(PIECE_UNICODE.get(p,'') for p in self.chess.captured['white'])
        b = ''.join(PIECE_UNICODE.get(p,'') for p in self.chess.captured['black'])
        self.cap_var.set(f"White took: {w}   Black took: {b}")

    # ── interaction ───────────────────────────────────────────────────────
    def _on_click(self, event):
        if self.ai_thinking or self.chess.turn != 'white':
            return
        status = self.chess.game_status()
        if status != 'playing':
            return

        c = event.x // CELL
        r = event.y // CELL
        if not (0 <= r < 8 and 0 <= c < 8):
            return

        piece = self.chess.board[r][c]

        if self.selected is None:
            # select own piece
            if piece and ChessBoard.color(piece) == 'white':
                self.selected = (r, c)
                self.valid_moves = [(fr,fc,tr,tc,fl) for fr,fc,tr,tc,fl
                                    in self.chess.legal_moves('white')
                                    if fr == r and fc == c]
        else:
            # try to move
            move = next((m for m in self.valid_moves if m[2] == r and m[3] == c), None)
            if move:
                fr, fc, tr, tc, flag = move
                promo = 'Q'
                if flag == 'promo':
                    promo = self._ask_promotion()
                self.chess.make_move(fr, fc, tr, tc, flag, promo)
                self.last_move = (fr, fc, tr, tc)
                self.selected = None
                self.valid_moves = []
                self.draw_board()
                self._check_game_over()
                if self.chess.game_status() == 'playing':
                    self._trigger_ai()
            elif piece and ChessBoard.color(piece) == 'white':
                # re-select
                self.selected = (r, c)
                self.valid_moves = [(fr,fc,tr,tc,fl) for fr,fc,tr,tc,fl
                                    in self.chess.legal_moves('white')
                                    if fr == r and fc == c]
            else:
                self.selected = None
                self.valid_moves = []
        self.draw_board()

    def _ask_promotion(self):
        win = tk.Toplevel(self)
        win.title("Promote Pawn")
        win.grab_set()
        win.resizable(False, False)
        choice = tk.StringVar(value='Q')
        tk.Label(win, text="Choose promotion:", font=("Helvetica", 12)).pack(pady=8)
        for p, sym in [('Q','♕ Queen'),('R','♖ Rook'),('B','♗ Bishop'),('N','♘ Knight')]:
            tk.Radiobutton(win, text=sym, variable=choice, value=p,
                           font=("Helvetica", 12)).pack(anchor='w', padx=20)
        tk.Button(win, text="OK", command=win.destroy,
                  font=("Helvetica", 11)).pack(pady=8)
        self.wait_window(win)
        return choice.get()

    def _trigger_ai(self):
        self.ai_thinking = True
        self._update_status()
        self.canvas.update()
        thread = threading.Thread(target=self._ai_move, daemon=True)
        thread.start()

    def _ai_move(self):
        move = self.ai.get_move(self.chess)
        self.after(0, lambda: self._apply_ai_move(move))

    def _apply_ai_move(self, move):
        self.ai_thinking = False
        if move:
            fr, fc, tr, tc, flag = move
            self.chess.make_move(fr, fc, tr, tc, flag, 'Q')
            self.last_move = (fr, fc, tr, tc)
        self.draw_board()
        self._check_game_over()

    def _check_game_over(self):
        status = self.chess.game_status()
        if status == 'playing':
            return
        self.draw_board()
        msgs = {
            'checkmate_white': "♛ Checkmate! White wins! 🎉",
            'checkmate_black': "♛ Checkmate! Black (AI) wins!",
            'stalemate': "Stalemate – it's a draw!",
            'draw': "Draw by 50-move rule!",
        }
        msg = msgs.get(status, "Game Over")
        self.after(300, lambda: messagebox.showinfo("Game Over", msg))

    def _on_diff_change(self, _event=None):
        d = self.diff_var.get().lower()
        self.ai.difficulty = d

    def new_game(self):
        self.chess.reset()
        self.selected = None
        self.valid_moves = []
        self.last_move = None
        self.ai_thinking = False
        self._on_diff_change()
        self.draw_board()


# ─────────────────────────────────────────────────────────────────────────────
if __name__ == '__main__':
    app = ChessApp()
    app.mainloop()
