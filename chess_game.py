"""
Chess Game in Python - Tkinter GUI with 3 AI difficulty levels
  Easy   → random legal moves
  Medium → 1-ply minimax with basic piece values
  Hard   → 3-ply minimax with alpha-beta pruning + positional tables
"""
# Module docstring describing the chess game and its three AI difficulty modes

import tkinter as tk                  # Import tkinter for building the GUI window
from tkinter import messagebox, ttk   # Import messagebox for popups and ttk for styled widgets
import random                         # Import random for the easy AI's random move selection
import copy                           # Import copy (available for deep-copying objects if needed)
import threading                      # Import threading so the AI runs without freezing the GUI

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────────────────────────────────

LIGHT = "#F0D9B5"   # Hex color for light-colored board squares (cream/beige)
DARK  = "#B58863"   # Hex color for dark-colored board squares (brown)
HIGH  = "#ACEA6A"   # Hex color used to highlight selected squares and valid move targets
LAST  = "#CDD16E"   # Hex color used to highlight the last move's from/to squares
CHECK = "#FF6B6B"   # Hex color used to highlight the king's square when it is in check

PIECE_UNICODE = {
    # Dictionary mapping piece letter codes to their Unicode chess symbols
    'K': '♔', 'Q': '♕', 'R': '♖', 'B': '♗', 'N': '♘', 'P': '♙',   # White pieces (uppercase)
    'k': '♚', 'q': '♛', 'r': '♜', 'b': '♝', 'n': '♞', 'p': '♟',   # Black pieces (lowercase)
}

PIECE_VALUES = {'P': 100, 'N': 320, 'B': 330, 'R': 500, 'Q': 900, 'K': 20000,   # Positive values for white pieces
                'p': -100, 'n': -320, 'b': -330, 'r': -500, 'q': -900, 'k': -20000}  # Negative values for black pieces

# Positional bonus tables (white perspective; mirrored for black)
# Each table has 64 values — one per square — ranking how good that square is for that piece type

PAWN_TABLE = [          # Positional bonus table for pawns (white perspective, row 0 = rank 8)
     0,  0,  0,  0,  0,  0,  0,  0,    # Rank 8 — pawns never start/stay here (would promote)
    50, 50, 50, 50, 50, 50, 50, 50,    # Rank 7 — pawns here are one step from promotion (big bonus)
    10, 10, 20, 30, 30, 20, 10, 10,    # Rank 6 — advanced pawns in center get moderate bonus
     5,  5, 10, 25, 25, 10,  5,  5,    # Rank 5 — center pawns slightly rewarded
     0,  0,  0, 20, 20,  0,  0,  0,    # Rank 4 — central e/d pawns on 4th rank get small bonus
     5, -5,-10,  0,  0,-10, -5,  5,    # Rank 3 — wing pawns slightly penalized if advanced sideways
     5, 10, 10,-20,-20, 10, 10,  5,    # Rank 2 — penalize center pawns staying at start; wings ok
     0,  0,  0,  0,  0,  0,  0,  0,   # Rank 1 — pawns can't be here for white
]
KNIGHT_TABLE = [        # Positional bonus table for knights
    -50,-40,-30,-30,-30,-30,-40,-50,   # Corners and edges are very bad for knights
    -40,-20,  0,  0,  0,  0,-20,-40,   # Near-edge squares still poor
    -30,  0, 10, 15, 15, 10,  0,-30,   # Knights gain value as they approach the center
    -30,  5, 15, 20, 20, 15,  5,-30,   # Central squares give the best bonus
    -30,  0, 15, 20, 20, 15,  0,-30,   # Same central bonus mirrored
    -30,  5, 10, 15, 15, 10,  5,-30,   # Slightly less bonus slightly further from center
    -40,-20,  0,  5,  5,  0,-20,-40,   # Near edges again; penalty returns
    -50,-40,-30,-30,-30,-30,-40,-50,   # Corners worst again (symmetric with top row)
]
BISHOP_TABLE = [        # Positional bonus table for bishops
    -20,-10,-10,-10,-10,-10,-10,-20,   # Board edges are bad for bishops
    -10,  0,  0,  0,  0,  0,  0,-10,  # Second-row squares are neutral
    -10,  0,  5, 10, 10,  5,  0,-10,  # Diagonals into center gain small bonus
    -10,  5,  5, 10, 10,  5,  5,-10,  # Off-center but active squares
    -10,  0, 10, 10, 10, 10,  0,-10,  # Central diagonal coverage rewarded
    -10, 10, 10, 10, 10, 10, 10,-10,  # Active rank with many diagonal options
    -10,  5,  0,  0,  0,  0,  5,-10,  # Near home rank, only flanks get tiny bonus
    -20,-10,-10,-10,-10,-10,-10,-20,  # Back rank edges are worst
]
ROOK_TABLE = [          # Positional bonus table for rooks
     0,  0,  0,  0,  0,  0,  0,  0,   # Back rank — neutral (rooks start here)
     5, 10, 10, 10, 10, 10, 10,  5,   # 7th rank is very powerful for rooks (bonus)
    -5,  0,  0,  0,  0,  0,  0, -5,   # Slight penalty for being on 3rd rank without activity
    -5,  0,  0,  0,  0,  0,  0, -5,   # Similar slight penalty
    -5,  0,  0,  0,  0,  0,  0, -5,   # Middle ranks are slightly penalized (rooks need open files)
    -5,  0,  0,  0,  0,  0,  0, -5,   # Same small penalty continues
    -5,  0,  0,  0,  0,  0,  0, -5,   # Rooks don't benefit from being stuck mid-board passively
     0,  0,  0,  5,  5,  0,  0,  0,   # Small bonus for d/e file rooks at starting rank (open file prep)
]
QUEEN_TABLE = [         # Positional bonus table for queens
    -20,-10,-10, -5, -5,-10,-10,-20,   # Corners and edges are bad for queens
    -10,  0,  0,  0,  0,  0,  0,-10,  # Near edges, neutral
    -10,  0,  5,  5,  5,  5,  0,-10,  # Slightly active central position
     -5,  0,  5,  5,  5,  5,  0, -5,  # Good central control
      0,  0,  5,  5,  5,  5,  0, -5,  # Strong central squares for the queen
    -10,  5,  5,  5,  5,  5,  0,-10,  # Active rank — queen controls lots of diagonals/files
    -10,  0,  5,  0,  0,  0,  0,-10,  # Near home rank
    -20,-10,-10, -5, -5,-10,-10,-20,  # Back rank edges worst (symmetric with top)
]
KING_TABLE = [          # Positional bonus table for king (middlegame — stay safe near corner)
    -30,-40,-40,-50,-50,-40,-40,-30,   # Center of board is most dangerous for king
    -30,-40,-40,-50,-50,-40,-40,-30,   # Same high danger — king exposed in middle ranks
    -30,-40,-40,-50,-50,-40,-40,-30,   # Still very dangerous
    -30,-40,-40,-50,-50,-40,-40,-30,   # King must avoid center at all costs
    -20,-30,-30,-40,-40,-30,-30,-20,   # 4th rank — slightly less dangerous but still bad
    -10,-20,-20,-20,-20,-20,-20,-10,   # 3rd rank — moderate danger
     20, 20,  0,  0,  0,  0, 20, 20,   # 2nd rank — flanks are safe (castled position)
     20, 30, 10,  0,  0, 10, 30, 20,   # Back rank — corners (castled) are the best for king safety
]

POS_TABLES = {
    # Map each piece type letter to its corresponding positional bonus table
    'P': PAWN_TABLE, 'N': KNIGHT_TABLE, 'B': BISHOP_TABLE,  # Pawn, Knight, Bishop tables
    'R': ROOK_TABLE, 'Q': QUEEN_TABLE,  'K': KING_TABLE,    # Rook, Queen, King tables
}


# ─────────────────────────────────────────────────────────────────────────────
# CHESS LOGIC
# ─────────────────────────────────────────────────────────────────────────────
class ChessBoard:
    # Class representing the full chess board state and all game logic
    def __init__(self):
        self.reset()   # Initialize the board by calling reset on construction

    def reset(self):
        # Reset the board to the standard chess starting position
        self.board = [
            # 2D list: row 0 = rank 8 (black's back rank), row 7 = rank 1 (white's back rank)
            ['r','n','b','q','k','b','n','r'],   # Row 0: black back rank
            ['p','p','p','p','p','p','p','p'],   # Row 1: black pawns
            [None]*8, [None]*8, [None]*8, [None]*8,  # Rows 2–5: empty squares
            ['P','P','P','P','P','P','P','P'],   # Row 6: white pawns
            ['R','N','B','Q','K','B','N','R'],   # Row 7: white back rank
        ]
        self.turn = 'white'   # White always moves first
        self.castling = {'K': True, 'Q': True, 'k': True, 'q': True}   # All four castling rights start available
        self.en_passant = None      # No en passant target square at the start; set after a double pawn push
        self.move_history = []      # List to record every move made (used for undo/review)
        self.captured = {'white': [], 'black': []}   # Track pieces captured by each side
        self.halfmove_clock = 0     # Counts half-moves since last capture/pawn move (for 50-move rule)
        self.fullmove_number = 1    # Full move counter; increments after black's move

    # ── helpers ──────────────────────────────────────────────────────────────
    @staticmethod
    def is_white(p): return p is not None and p.isupper()   # True if piece is a white piece (uppercase letter)

    @staticmethod
    def is_black(p): return p is not None and p.islower()   # True if piece is a black piece (lowercase letter)

    @staticmethod
    def color(p):
        # Return 'white', 'black', or None depending on the piece character
        if p is None: return None                             # Empty square has no color
        return 'white' if p.isupper() else 'black'           # Uppercase = white, lowercase = black

    def enemy(self, color): return 'black' if color == 'white' else 'white'   # Return the opposite color

    def piece_at(self, r, c):
        # Safely return the piece at (r, c), or None if out of bounds
        if 0 <= r < 8 and 0 <= c < 8:
            return self.board[r][c]   # Return piece if coordinates are within the board
        return None                   # Return None for out-of-bounds coordinates

    def find_king(self, color):
        # Find and return (row, col) of the king of the given color on the current board
        k = 'K' if color == 'white' else 'k'   # Determine king character based on color
        for r in range(8):                       # Iterate over all rows
            for c in range(8):                   # Iterate over all columns
                if self.board[r][c] == k:
                    return r, c                  # Return position as soon as king is found
        return None                              # Return None if king not found (shouldn't happen normally)

    # ── raw move generation (does NOT check legality re: own-king safety) ──
    def pseudo_moves(self, r, c, board=None):
        # Generate all pseudo-legal moves for the piece at (r, c) without checking if king is left in check
        if board is None: board = self.board     # Use the current board state if none is provided
        piece = board[r][c]                      # Get the piece at the given square
        if piece is None: return []              # No piece here — return empty list
        color = 'white' if piece.isupper() else 'black'   # Determine color from case
        moves = []                               # List to collect all candidate moves
        p = piece.upper()                        # Normalize piece to uppercase for switch logic

        def add(nr, nc, flag=None):
            # Helper: add a move to (nr, nc) if in bounds and not occupied by a friendly piece
            if 0 <= nr < 8 and 0 <= nc < 8:
                target = board[nr][nc]                              # Get piece at target square
                if target is None or self.color(target) != color:  # Allow move if empty or enemy piece
                    moves.append((nr, nc, flag))                    # Append the target square and optional flag

        def slide(dr, dc):
            # Helper: generate sliding moves (bishop, rook, queen) in direction (dr, dc)
            nr, nc = r+dr, c+dc                  # Start one step in the given direction
            while 0 <= nr < 8 and 0 <= nc < 8:  # Continue while still on the board
                target = board[nr][nc]
                if target is None:
                    moves.append((nr, nc, None)) # Empty square — add move and keep sliding
                elif self.color(target) != color:
                    moves.append((nr, nc, None)); break  # Enemy piece — capture and stop sliding
                else:
                    break                        # Friendly piece — blocked, stop sliding
                nr += dr; nc += dc               # Advance one more step in the same direction

        if p == 'P':
            # Pawn move generation
            d = -1 if color == 'white' else 1    # White pawns move up (negative row), black move down
            start_row = 6 if color == 'white' else 1   # Starting row for double-push eligibility
            # forward one square
            if 0 <= r+d < 8 and board[r+d][c] is None:
                moves.append((r+d, c, 'promo' if r+d in (0,7) else None))   # Promote if reaching back rank
                if r == start_row and board[r+2*d][c] is None:
                    moves.append((r+2*d, c, 'double'))   # Double push from starting row if path is clear
            # diagonal captures
            for dc in (-1, 1):                   # Check both diagonal capture directions
                nr, nc = r+d, c+dc
                if 0 <= nr < 8 and 0 <= nc < 8:
                    target = board[nr][nc]
                    if target is not None and self.color(target) != color:
                        moves.append((nr, nc, 'promo' if nr in (0,7) else None))  # Capture with possible promotion
                    elif (nr, nc) == self.en_passant:
                        moves.append((nr, nc, 'ep'))     # En passant capture
        elif p == 'N':
            # Knight move generation — all 8 L-shaped jumps
            for dr, dc in [(-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)]:
                add(r+dr, c+dc)                  # Add each L-shape destination if valid
        elif p == 'B':
            # Bishop move generation — slide along all 4 diagonals
            for dr, dc in [(-1,-1),(-1,1),(1,-1),(1,1)]: slide(dr, dc)
        elif p == 'R':
            # Rook move generation — slide along all 4 straight directions
            for dr, dc in [(-1,0),(1,0),(0,-1),(0,1)]: slide(dr, dc)
        elif p == 'Q':
            # Queen move generation — combination of rook and bishop (all 8 directions)
            for dr, dc in [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]: slide(dr, dc)
        elif p == 'K':
            # King move generation — one step in any of 8 directions
            for dr, dc in [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]: add(r+dr, c+dc)
            # castling (kingside and queenside)
            row = 7 if color == 'white' else 0   # King's home row depending on color
            if r == row and c == 4:              # King must be on its starting square to castle
                if color == 'white' and self.castling['K']:
                    if board[row][5] is None and board[row][6] is None:   # Squares between king and rook must be empty
                        moves.append((row, 6, 'castle_k'))                 # Add kingside castling move
                if color == 'white' and self.castling['Q']:
                    if board[row][3] is None and board[row][2] is None and board[row][1] is None:  # Three squares must be empty
                        moves.append((row, 2, 'castle_q'))                 # Add queenside castling move
                if color == 'black' and self.castling['k']:
                    if board[row][5] is None and board[row][6] is None:   # Same check for black kingside
                        moves.append((row, 6, 'castle_k'))
                if color == 'black' and self.castling['q']:
                    if board[row][3] is None and board[row][2] is None and board[row][1] is None:  # Same check for black queenside
                        moves.append((row, 2, 'castle_q'))
        return moves   # Return the complete list of pseudo-legal moves

    def is_square_attacked(self, r, c, by_color, board=None):
        # Return True if square (r, c) is attacked by any piece of by_color
        if board is None: board = self.board     # Use current board if none provided
        for rr in range(8):                      # Iterate over all rows
            for cc in range(8):                  # Iterate over all columns
                p = board[rr][cc]
                if p is not None and self.color(p) == by_color:   # Found an enemy piece
                    for nr, nc, _ in self.pseudo_moves(rr, cc, board):
                        if nr == r and nc == c:
                            return True          # This enemy piece attacks (r, c)
        return False                             # No enemy piece attacks this square

    def in_check(self, color, board=None):
        # Return True if the king of the given color is currently in check
        if board is None: board = self.board
        kr, kc = self.find_king_b(color, board)  # Find the king's position on the given board
        if kr is None: return False              # No king found — can't be in check
        return self.is_square_attacked(kr, kc, self.enemy(color), board)   # Check if any enemy attacks the king

    def find_king_b(self, color, board):
        # Like find_king but works on any board state passed in (used for hypothetical positions)
        k = 'K' if color == 'white' else 'k'    # King character for the given color
        for r in range(8):
            for c in range(8):
                if board[r][c] == k:
                    return r, c                  # Return king's position
        return None, None                        # King not found — returns (None, None)

    def apply_move_to_board(self, board, r, c, nr, nc, flag, promo='Q'):
        """Returns new board state (list of lists) after applying move."""
        # Create a deep copy of the board to avoid mutating the original
        b = [row[:] for row in board]            # Shallow copy each row (pieces are immutable strings/None)
        piece = b[r][c]                          # Get the moving piece
        color = 'white' if piece.isupper() else 'black'   # Determine its color

        b[nr][nc] = piece    # Place piece on the destination square
        b[r][c] = None       # Clear the origin square

        if flag == 'promo':
            b[nr][nc] = promo if color == 'white' else promo.lower()   # Replace pawn with chosen promotion piece
        elif flag == 'ep':
            ep_r = nr + (1 if color == 'white' else -1)   # The captured pawn is one row behind the en passant target
            b[ep_r][nc] = None                             # Remove the captured pawn
        elif flag in ('castle_k', 'castle_q'):
            row = r                              # Castling happens on the king's starting row
            if flag == 'castle_k':
                b[row][5] = b[row][7]; b[row][7] = None   # Move kingside rook from h-file to f-file
            else:
                b[row][3] = b[row][0]; b[row][0] = None   # Move queenside rook from a-file to d-file
        return b   # Return the new board state

    def legal_moves(self, color=None, board=None):
        # Generate all fully legal moves (pseudo-legal minus moves that leave own king in check)
        if color is None: color = self.turn      # Default to the current turn's color
        if board is None: board = self.board     # Default to the current board
        result = []                              # Will hold all legal moves
        for r in range(8):
            for c in range(8):
                p = board[r][c]
                if p is None or self.color(p) != color: continue   # Skip squares with no piece or enemy pieces
                for nr, nc, flag in self.pseudo_moves(r, c, board):
                    # For castling, also check intermediate squares
                    if flag == 'castle_k':
                        if self.in_check(color, board): continue   # Can't castle while in check
                        mid_b = self.apply_move_to_board(board, r, c, r, c+1, None)
                        if self.in_check(color, mid_b): continue   # Can't castle through check (kingside middle square)
                    elif flag == 'castle_q':
                        if self.in_check(color, board): continue   # Can't castle while in check
                        mid_b = self.apply_move_to_board(board, r, c, r, c-1, None)
                        if self.in_check(color, mid_b): continue   # Can't castle through check (queenside middle square)
                    nb = self.apply_move_to_board(board, r, c, nr, nc, flag)   # Apply the move hypothetically
                    if not self.in_check(color, nb):
                        result.append((r, c, nr, nc, flag))   # Only keep the move if king is not in check afterward
        return result   # Return all legal moves

    def make_move(self, r, c, nr, nc, flag, promo='Q'):
        # Apply a move permanently to the actual board state
        piece = self.board[r][c]    # Get the piece being moved
        color = self.turn           # Current player's color
        captured = self.board[nr][nc]   # Piece on the destination (may be None)

        # en passant capture
        if flag == 'ep':
            ep_r = nr + (1 if color == 'white' else -1)   # Row of the captured pawn (behind target square)
            captured = self.board[ep_r][nc]                # Store the en passant captured pawn
            self.board[ep_r][nc] = None                    # Remove the captured pawn from the board

        self.board[nr][nc] = piece   # Place the moving piece on its destination
        self.board[r][c] = None      # Clear the piece's original square

        if captured:
            self.captured[color].append(captured)   # Record captured piece for display

        if flag == 'promo':
            self.board[nr][nc] = promo if color == 'white' else promo.lower()   # Replace pawn with promotion piece
        elif flag == 'castle_k':
            self.board[nr][5] = self.board[nr][7]; self.board[nr][7] = None   # Move kingside rook
        elif flag == 'castle_q':
            self.board[nr][3] = self.board[nr][0]; self.board[nr][0] = None   # Move queenside rook

        # update castling rights
        if piece == 'K': self.castling['K'] = self.castling['Q'] = False   # White king moved — no more castling for white
        if piece == 'k': self.castling['k'] = self.castling['q'] = False   # Black king moved — no more castling for black
        if piece == 'R' and r == 7:
            if c == 7: self.castling['K'] = False   # White kingside rook moved
            if c == 0: self.castling['Q'] = False   # White queenside rook moved
        if piece == 'r' and r == 0:
            if c == 7: self.castling['k'] = False   # Black kingside rook moved
            if c == 0: self.castling['q'] = False   # Black queenside rook moved

        # en passant target
        self.en_passant = (nr + (1 if color=='white' else -1), nc) if flag == 'double' else None   # Set en passant target if double pawn push; otherwise clear it

        self.move_history.append((r, c, nr, nc, flag, piece, captured))   # Record move details in history
        self.turn = self.enemy(color)   # Switch the turn to the other player

        if color == 'black':
            self.fullmove_number += 1   # Increment full move counter after black's move

    def game_status(self):
        """Returns: 'playing', 'checkmate_white', 'checkmate_black', 'stalemate', 'draw'"""
        moves = self.legal_moves(self.turn)   # Get all legal moves for the current player
        if moves:
            # Fifty-move rule (simplified)
            if self.halfmove_clock >= 100:
                return 'draw'              # 50 full moves without capture or pawn move — draw
            return 'playing'               # Moves available and no draw condition — game continues
        if self.in_check(self.turn):
            return f'checkmate_{self.enemy(self.turn)}'   # No moves and in check — checkmate; opponent wins
        return 'stalemate'                 # No moves but not in check — stalemate


# ─────────────────────────────────────────────────────────────────────────────
# AI ENGINE
# ─────────────────────────────────────────────────────────────────────────────
class ChessAI:
    # Class encapsulating the chess AI logic for all three difficulty levels
    def __init__(self, difficulty='medium'):
        self.difficulty = difficulty  # Store difficulty level: 'easy', 'medium', or 'hard'

    def get_move(self, chess: ChessBoard):
        # Choose and return the best move for black based on current difficulty
        moves = chess.legal_moves('black')   # Get all legal moves available to black
        if not moves:
            return None                      # No moves available — game is over
        if self.difficulty == 'easy':
            return self._random_move(moves)                    # Easy: pick a random legal move
        elif self.difficulty == 'medium':
            return self._minimax_move(chess, moves, depth=2)   # Medium: 2-ply minimax search
        else:
            return self._minimax_move(chess, moves, depth=3)   # Hard: 3-ply minimax with alpha-beta pruning

    def _random_move(self, moves):
        return random.choice(moves)   # Return a random move from the list of legal moves

    def _minimax_move(self, chess: ChessBoard, moves, depth):
        # Find the best move for black by searching 'depth' plies ahead using minimax
        best_score = float('-inf')   # Start with worst possible score (for black, maximizing)
        best_move = moves[0]         # Default to first move in case all have equal score
        alpha, beta = float('-inf'), float('inf')   # Initialize alpha-beta bounds
        random.shuffle(moves)        # Shuffle to introduce variety when scores are equal
        for move in moves:
            nb = chess.apply_move_to_board(chess.board, *move[:4], move[4])   # Apply move hypothetically
            score = self._minimax(chess, nb, depth - 1, alpha, beta, True)    # Evaluate resulting position (white to move next = maximizing)
            if score > best_score:
                best_score = score   # Update best score if this move is better
                best_move = move     # Track the best move found so far
            alpha = max(alpha, score)   # Update alpha for pruning
        return best_move              # Return the move with the highest evaluated score

    def _minimax(self, chess: ChessBoard, board, depth, alpha, beta, is_max):
        # Recursive minimax function with alpha-beta pruning
        color = 'white' if is_max else 'black'   # Determine whose turn it is at this node
        moves = chess.legal_moves(color, board)   # Get all legal moves for this color

        if depth == 0 or not moves:
            return self._evaluate(chess, board)   # Base case: evaluate and return static score

        if is_max:
            # Maximizing node (white's turn — trying to maximize score)
            best = float('-inf')
            for move in moves:
                nb = chess.apply_move_to_board(board, *move[:4], move[4])             # Apply move
                best = max(best, self._minimax(chess, nb, depth-1, alpha, beta, False))  # Recurse for black
                alpha = max(alpha, best)   # Update alpha
                if beta <= alpha: break    # Beta cutoff — prune remaining branches
            return best
        else:
            # Minimizing node (black's turn — trying to minimize score)
            best = float('inf')
            for move in moves:
                nb = chess.apply_move_to_board(board, *move[:4], move[4])            # Apply move
                best = min(best, self._minimax(chess, nb, depth-1, alpha, beta, True))  # Recurse for white
                beta = min(beta, best)    # Update beta
                if beta <= alpha: break   # Alpha cutoff — prune remaining branches
            return best

    def _evaluate(self, chess: ChessBoard, board):
        # Static evaluation function — returns a score from black's perspective (positive = good for black)
        score = 0
        for r in range(8):
            for c in range(8):
                p = board[r][c]
                if p is None: continue              # Skip empty squares
                val = PIECE_VALUES.get(p, 0)        # Get the material value of the piece
                # positional bonus
                pu = p.upper()                      # Normalize to uppercase for table lookup
                if pu in POS_TABLES:
                    if chess.is_white(p):
                        pos = POS_TABLES[pu][r * 8 + c]           # White piece: use table index directly
                    else:
                        pos = -POS_TABLES[pu][(7 - r) * 8 + c]   # Black piece: mirror vertically and negate
                else:
                    pos = 0                         # No positional table for this piece type
                score += val + pos                  # Accumulate material + positional score
        return score   # Return total evaluation score


# ─────────────────────────────────────────────────────────────────────────────
# GUI
# ─────────────────────────────────────────────────────────────────────────────
CELL = 72   # Size of each board square in pixels

class ChessApp(tk.Tk):
    # Main application window — extends Tk to serve as the root GUI window
    def __init__(self):
        super().__init__()                      # Initialize the Tk root window
        self.title("♟ Python Chess")            # Set the window title bar text
        self.resizable(False, False)            # Prevent window resizing in both directions
        self.configure(bg="#2c2c2c")            # Set dark background color for the window

        self.chess = ChessBoard()               # Create a new chess board game state
        self.ai = ChessAI('medium')             # Create an AI opponent set to medium difficulty
        self.selected = None                    # Tracks the currently selected square (row, col) or None
        self.valid_moves = []                   # List of legal moves for the selected piece
        self.last_move = None                   # Stores (fr, fc, tr, tc) of the last move played
        self.ai_thinking = False                # Flag to prevent player input while AI is computing
        self.player_color = 'white'             # Player always controls white pieces
        self.promotion_choice = 'Q'             # Default promotion piece is Queen

        self._build_ui()                        # Build and layout all UI widgets
        self.draw_board()                       # Draw the initial board state

    # ── UI layout ─────────────────────────────────────────────────────────
    def _build_ui(self):
        # Construct the full user interface layout
        # top bar
        top = tk.Frame(self, bg="#2c2c2c")      # Container frame for the top bar (difficulty + new game)
        top.pack(fill='x', padx=10, pady=(10, 0))   # Pack it to fill horizontally with padding

        tk.Label(top, text="Difficulty:", bg="#2c2c2c", fg="white",
                 font=("Helvetica", 12)).pack(side='left')   # Label for the difficulty dropdown
        self.diff_var = tk.StringVar(value='Medium')         # StringVar to track current difficulty selection
        diff_menu = ttk.Combobox(top, textvariable=self.diff_var,
                                 values=['Easy', 'Medium', 'Hard'],
                                 state='readonly', width=8, font=("Helvetica", 11))   # Dropdown for difficulty
        diff_menu.pack(side='left', padx=6)                  # Place dropdown next to the label
        diff_menu.bind('<<ComboboxSelected>>', self._on_diff_change)   # Trigger callback when selection changes

        tk.Button(top, text="New Game", command=self.new_game,
                  bg="#4CAF50", fg="white", font=("Helvetica", 11, "bold"),
                  relief='flat', padx=10, pady=3).pack(side='right')   # Green "New Game" button on the right

        # main area
        main = tk.Frame(self, bg="#2c2c2c")     # Central frame containing rank labels + canvas
        main.pack(padx=10, pady=8)              # Pack with padding

        # rank labels left
        left_labels = tk.Frame(main, bg="#2c2c2c")   # Frame to hold the 8–1 rank labels on the left
        left_labels.grid(row=0, column=0)             # Place in grid to the left of the canvas
        for i, lbl in enumerate("87654321"):
            tk.Label(left_labels, text=lbl, bg="#2c2c2c", fg="#aaa",
                     font=("Helvetica", 10), width=2).grid(row=i)   # One label per rank, aligned with board rows

        # canvas
        self.canvas = tk.Canvas(main, width=CELL*8, height=CELL*8,
                                 highlightthickness=2, highlightbackground="#888")   # 576x576 px board canvas
        self.canvas.grid(row=0, column=1)         # Place canvas in the center column
        self.canvas.bind("<Button-1>", self._on_click)   # Bind left mouse click to click handler

        # file labels bottom
        bot_labels = tk.Frame(main, bg="#2c2c2c")   # Frame to hold the a–h file labels below the board
        bot_labels.grid(row=1, column=1)             # Place below the canvas
        for lbl in "abcdefgh":
            tk.Label(bot_labels, text=lbl, bg="#2c2c2c", fg="#aaa",
                     font=("Helvetica", 10), width=int(CELL/9)+1).pack(side='left')   # One label per file, evenly spaced

        # status / captured
        bottom = tk.Frame(self, bg="#2c2c2c")    # Bottom frame for status text and captured pieces
        bottom.pack(fill='x', padx=10, pady=(0, 10))   # Pack at bottom with horizontal fill

        self.status_var = tk.StringVar(value="Your turn (White)")   # StringVar for the turn/status message
        tk.Label(bottom, textvariable=self.status_var, bg="#2c2c2c", fg="#e0e0e0",
                 font=("Helvetica", 12, "bold")).pack(side='left')   # Status label on the left

        self.cap_var = tk.StringVar(value="")    # StringVar showing captured pieces
        tk.Label(bottom, textvariable=self.cap_var, bg="#2c2c2c", fg="#aaa",
                 font=("Helvetica", 10)).pack(side='right')   # Captured pieces label on the right

    # ── drawing ───────────────────────────────────────────────────────────
    def draw_board(self):
        # Redraw the entire board canvas from scratch
        self.canvas.delete('all')   # Clear all existing canvas drawings
        in_check_sq = None
        if self.chess.in_check(self.chess.turn):
            in_check_sq = self.chess.find_king_b(self.chess.turn, self.chess.board)   # Find king to highlight if in check

        for r in range(8):
            for c in range(8):
                x1, y1 = c*CELL, r*CELL       # Top-left pixel of the square
                x2, y2 = x1+CELL, y1+CELL     # Bottom-right pixel of the square

                # base color
                base = LIGHT if (r+c) % 2 == 0 else DARK   # Alternate light/dark based on parity

                # override with highlight
                sq = (r, c)
                if self.last_move and sq in (self.last_move[:2], self.last_move[2:4]):
                    color = LAST             # Highlight last move's origin and destination
                elif in_check_sq and sq == in_check_sq:
                    color = CHECK            # Highlight king's square red when in check
                elif self.selected and sq == self.selected:
                    color = HIGH             # Highlight the selected piece's square
                elif sq in [(m[2], m[3]) for m in self.valid_moves]:
                    color = HIGH             # Highlight valid destination squares
                else:
                    color = base             # Use default light/dark color

                self.canvas.create_rectangle(x1, y1, x2, y2, fill=color, outline='')   # Draw square

                # dot for valid move (empty square)
                if sq in [(m[2], m[3]) for m in self.valid_moves]:
                    piece = self.chess.board[r][c]
                    if piece is None:
                        cx, cy = x1+CELL//2, y1+CELL//2   # Center of the square
                        self.canvas.create_oval(cx-10, cy-10, cx+10, cy+10,
                                                fill="#44AA44", outline='')   # Draw green dot on empty valid squares

                # piece
                piece = self.chess.board[r][c]
                if piece:
                    sym = PIECE_UNICODE.get(piece, piece)   # Get Unicode chess symbol for the piece
                    self.canvas.create_text(x1+CELL//2, y1+CELL//2, text=sym,
                                            font=("Arial", int(CELL*0.62)),
                                            fill='white' if piece.isupper() else '#111')   # White pieces in white, black in near-black

        self._update_status()      # Refresh the status label text
        self._update_captured()    # Refresh the captured pieces display

    def _update_status(self):
        # Update the status label based on the current game state
        status = self.chess.game_status()   # Get current game status string
        turn = self.chess.turn
        if status == 'playing':
            check = " ⚠ CHECK!" if self.chess.in_check(turn) else ""   # Append check warning if applicable
            if turn == 'white':
                self.status_var.set(f"Your turn (White){check}")        # Prompt human player
            else:
                txt = "🤖 AI thinking..." if self.ai_thinking else f"AI's turn (Black){check}"   # Show AI status
                self.status_var.set(txt)
        elif 'checkmate' in status:
            winner = 'White' if 'white' in status else 'Black'
            self.status_var.set(f"♛ Checkmate! {winner} wins!")         # Announce checkmate winner
        elif status == 'stalemate':
            self.status_var.set("Stalemate – It's a draw!")             # Announce stalemate
        elif status == 'draw':
            self.status_var.set("Draw by 50-move rule!")                # Announce 50-move draw

    def _update_captured(self):
        # Update the captured pieces display string using Unicode symbols
        w = ''.join(PIECE_UNICODE.get(p,'') for p in self.chess.captured['white'])   # White's captured pieces as symbols
        b = ''.join(PIECE_UNICODE.get(p,'') for p in self.chess.captured['black'])   # Black's captured pieces as symbols
        self.cap_var.set(f"White took: {w}   Black took: {b}")   # Display both side's captures

    # ── interaction ───────────────────────────────────────────────────────
    def _on_click(self, event):
        # Handle mouse click on the board canvas
        if self.ai_thinking or self.chess.turn != 'white':
            return   # Ignore clicks while AI is computing or it's not the player's turn
        status = self.chess.game_status()
        if status != 'playing':
            return   # Ignore clicks if the game has already ended

        c = event.x // CELL   # Convert pixel x to column index
        r = event.y // CELL   # Convert pixel y to row index
        if not (0 <= r < 8 and 0 <= c < 8):
            return   # Ignore clicks outside the board bounds

        piece = self.chess.board[r][c]   # Get piece at the clicked square

        if self.selected is None:
            # select own piece
            if piece and ChessBoard.color(piece) == 'white':
                self.selected = (r, c)   # Mark this square as selected
                self.valid_moves = [(fr,fc,tr,tc,fl) for fr,fc,tr,tc,fl
                                    in self.chess.legal_moves('white')
                                    if fr == r and fc == c]   # Get all legal moves for the selected piece
        else:
            # try to move
            move = next((m for m in self.valid_moves if m[2] == r and m[3] == c), None)   # Check if clicked square is a valid destination
            if move:
                fr, fc, tr, tc, flag = move   # Unpack the chosen move
                promo = 'Q'
                if flag == 'promo':
                    promo = self._ask_promotion()   # Ask player what piece to promote to
                self.chess.make_move(fr, fc, tr, tc, flag, promo)   # Apply the move to the board
                self.last_move = (fr, fc, tr, tc)   # Record last move for visual highlighting
                self.selected = None               # Deselect after moving
                self.valid_moves = []              # Clear valid move highlights
                self.draw_board()                  # Redraw board after player's move
                self._check_game_over()            # Check if the game ended after this move
                if self.chess.game_status() == 'playing':
                    self._trigger_ai()             # Trigger AI response if game is still going
            elif piece and ChessBoard.color(piece) == 'white':
                # re-select
                self.selected = (r, c)             # Select a different white piece
                self.valid_moves = [(fr,fc,tr,tc,fl) for fr,fc,tr,tc,fl
                                    in self.chess.legal_moves('white')
                                    if fr == r and fc == c]   # Update valid moves for newly selected piece
            else:
                self.selected = None               # Click on empty/enemy square — deselect
                self.valid_moves = []              # Clear valid move list
        self.draw_board()   # Redraw to reflect new selection state

    def _ask_promotion(self):
        # Show a popup dialog asking the player to choose a promotion piece
        win = tk.Toplevel(self)          # Create a new top-level popup window
        win.title("Promote Pawn")        # Set popup title
        win.grab_set()                   # Make popup modal (block input to main window)
        win.resizable(False, False)      # Prevent resizing the popup
        choice = tk.StringVar(value='Q')   # Default promotion choice is Queen
        tk.Label(win, text="Choose promotion:", font=("Helvetica", 12)).pack(pady=8)   # Instruction label
        for p, sym in [('Q','♕ Queen'),('R','♖ Rook'),('B','♗ Bishop'),('N','♘ Knight')]:
            tk.Radiobutton(win, text=sym, variable=choice, value=p,
                           font=("Helvetica", 12)).pack(anchor='w', padx=20)   # Radio button for each piece option
        tk.Button(win, text="OK", command=win.destroy,
                  font=("Helvetica", 11)).pack(pady=8)   # OK button to confirm and close popup
        self.wait_window(win)            # Wait for the popup to close before continuing
        return choice.get()             # Return the selected promotion piece letter

    def _trigger_ai(self):
        # Start the AI move computation in a background thread
        self.ai_thinking = True          # Set flag to block player input during AI computation
        self._update_status()            # Show "AI thinking..." in the status label
        self.canvas.update()             # Force canvas to repaint immediately
        thread = threading.Thread(target=self._ai_move, daemon=True)   # Create background thread for AI
        thread.start()                   # Start the AI computation thread

    def _ai_move(self):
        # Run in background thread: compute the AI's best move
        move = self.ai.get_move(self.chess)              # Ask the AI for its best move
        self.after(0, lambda: self._apply_ai_move(move)) # Schedule move application on the main thread

    def _apply_ai_move(self, move):
        # Apply the AI's computed move on the main thread (thread-safe GUI update)
        self.ai_thinking = False   # Clear the AI thinking flag
        if move:
            fr, fc, tr, tc, flag = move              # Unpack the AI's chosen move
            self.chess.make_move(fr, fc, tr, tc, flag, 'Q')   # Apply the move (AI always promotes to Queen)
            self.last_move = (fr, fc, tr, tc)        # Record for last-move highlighting
        self.draw_board()          # Redraw board after AI move
        self._check_game_over()    # Check if the game has ended after the AI's move

    def _check_game_over(self):
        # Check if the game is over and show a popup message if so
        status = self.chess.game_status()
        if status == 'playing':
            return   # Game still in progress — do nothing
        self.draw_board()   # Final board redraw to show end state
        msgs = {
            # Map each terminal status to a display message
            'checkmate_white': "♛ Checkmate! White wins! 🎉",   # Human wins
            'checkmate_black': "♛ Checkmate! Black (AI) wins!", # AI wins
            'stalemate': "Stalemate – it's a draw!",            # Stalemate draw
            'draw': "Draw by 50-move rule!",                    # 50-move rule draw
        }
        msg = msgs.get(status, "Game Over")   # Get message or fallback to generic "Game Over"
        self.after(300, lambda: messagebox.showinfo("Game Over", msg))   # Show popup after 300ms delay

    def _on_diff_change(self, _event=None):
        # Called when the difficulty dropdown value changes
        d = self.diff_var.get().lower()   # Get the new difficulty as a lowercase string
        self.ai.difficulty = d            # Update the AI's difficulty setting

    def new_game(self):
        # Reset the entire game state to start a new game
        self.chess.reset()        # Reset the chess board to starting position
        self.selected = None      # Clear any selected square
        self.valid_moves = []     # Clear valid move highlights
        self.last_move = None     # Clear last move highlight
        self.ai_thinking = False  # Reset AI thinking flag
        self._on_diff_change()    # Re-apply the current difficulty setting to the AI
        self.draw_board()         # Redraw the board in its initial state


# ─────────────────────────────────────────────────────────────────────────────
if __name__ == '__main__':
    app = ChessApp()   # Create the main application window
    app.mainloop()     # Start the Tkinter event loop to keep the window open and responsive
