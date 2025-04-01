open Fstar_pluginlib

type token =
  | RAW_ID of string
  | TEXT of string
  | NONEMPTY_S
  | EQ
  | SLASH
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | LBRACK
  | RBRACK
  | POUND0
  | POUND1
  | POUND2
  | POUND3
  | POUND6
  | POUND7
  | DOTDOTDOT
  | DOTDOT
  | DOT
  | AMP
  | POUND
  | UINT of Prims.int
  | MINUS
  | SLASHSLASHEQ
  | SLASHEQ
  | SLASHSLASH
  | COMMA
  | ARROW
  | COLON
  | HAT
  | STAR
  | PLUS
  | DOLLARDOLLAR
  | DOLLAR
  | QUESTION
  | EOF
[@@deriving show]
