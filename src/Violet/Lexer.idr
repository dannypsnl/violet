module Violet.Lexer

import Text.Lexer
import Text.Token
import Data.List
import Data.SortedSet

%default total

public export
data VTokenKind
  = VTIdentifier        -- x
  | VTData              -- data
  | VTLet               -- let
  | VTElim              -- elim
  | VTPostulate         -- postulate
  | VTUniverse          -- U
  | VTVerticalLine      -- |
  | VTAssign            -- =
  | VTColon             -- :
  | VTSemicolon         -- ;
  | VTOpenP             -- (
  | VTCloseP            -- )
  | VTArrow             -- → or ->
  | VTLambda            -- λ or \
  | VTLambdaArrow       -- =>
  | VTDollar            -- $
  | VTIgnore            -- single line comment or whitespace
  | VTModule            -- module
  | VTImport            -- import

export
Eq VTokenKind where
  (==) VTIdentifier VTIdentifier = True
  (==) VTData VTData = True
  (==) VTLet VTLet = True
  (==) VTElim VTElim = True
  (==) VTPostulate VTPostulate = True
  (==) VTUniverse VTUniverse = True
  (==) VTVerticalLine VTVerticalLine = True
  (==) VTAssign VTAssign = True
  (==) VTColon VTColon = True
  (==) VTSemicolon VTSemicolon = True
  (==) VTOpenP VTOpenP = True
  (==) VTCloseP VTCloseP = True
  (==) VTArrow VTArrow = True
  (==) VTLambda VTLambda = True
  (==) VTLambdaArrow VTLambdaArrow = True
  (==) VTDollar VTDollar = True
  (==) VTModule VTModule = True
  (==) VTImport VTImport = True
  (==) _ _ = False

export
Show VTokenKind where
  show VTIdentifier   = "<identifer>"
  show VTData         = "data"
  show VTLet          = "let"
  show VTElim         = "elim"
  show VTPostulate    = "postulate"
  show VTUniverse     = "U"
  show VTAssign       = "="
  show VTColon        = ":"
  show VTSemicolon    = ";"
  show VTVerticalLine = "|"
  show VTOpenP        = "("
  show VTCloseP       = ")"
  show VTArrow        = "→"
  show VTLambda       = "λ"
  show VTLambdaArrow  = "=>"
  show VTDollar       = "$"
  show VTIgnore       = "<ignore>"
  show VTModule       = "module"
  show VTImport       = "import"

public export
VToken : Type
VToken = Token VTokenKind

export
Show VToken where
  show (Tok kind text) = "Tok kind: " ++ show kind ++ "\n text: " ++ text

export
TokenKind VTokenKind where
  TokType VTIdentifier = String
  TokType _ = ()

  tokValue VTIdentifier s = s
  tokValue VTData _ = ()
  tokValue VTLet _ = ()
  tokValue VTElim _ = ()
  tokValue VTPostulate _ = ()
  tokValue VTUniverse _ = ()
  tokValue VTVerticalLine _ = ()
  tokValue VTAssign _ = ()
  tokValue VTColon _ = ()
  tokValue VTSemicolon _ = ()
  tokValue VTOpenP _ = ()
  tokValue VTCloseP _ = ()
  tokValue VTArrow _ = ()
  tokValue VTLambda _ = ()
  tokValue VTLambdaArrow _ = ()
  tokValue VTDollar _ = ()
  tokValue VTIgnore _ = ()
  tokValue VTModule _ = ()
  tokValue VTImport _ = ()

||| An identifier starts from alphabet
||| following with alphabet, number, and the below set
||| `-`, `_`, `?`, `!`
isIdChar : Char -> Bool
isIdChar x = isAlphaNum x || (x `contains` fromList ['-', '_', '?', '!'])

isStartChar : Char -> Bool
isStartChar x = isAlpha x || (x `contains` fromList ['-', '_', '?', '!'])

identifier : Lexer
identifier = (pred isStartChar) <+> many (pred isIdChar)

-- 只要還沒碰到換行就是單行的註解內容
comment : Lexer
comment = is '-' <+> is '-' <+> many (isNot '\n')

keywords : List (String, VTokenKind)
keywords = [
  ("data", VTData),
  ("let", VTLet),
  ("elim", VTElim),
  ("postulate", VTPostulate),
  ("U", VTUniverse),
  ("module", VTModule),
  ("import", VTImport)
]

violetTokenMap : TokenMap VToken
violetTokenMap = toTokenMap [
    (spaces, VTIgnore),
    (comment, VTIgnore),
    (exact "->" <|> is '→', VTArrow),
    (is 'λ' <|> is '\\', VTLambda),
    (exact "=>" <|> is '⇒', VTLambdaArrow),
    (exact "|", VTVerticalLine),
    (exact ":", VTColon),
    (exact ";", VTSemicolon),
    (exact "$", VTDollar),
    (exact "(", VTOpenP),
    (exact ")", VTCloseP),
    (exact "=", VTAssign)
  ] ++
  [ (identifier, \s =>
      case lookup s keywords of
        (Just kind) => Tok kind s
        Nothing => Tok VTIdentifier s
    )
  ]

export
lexViolet : String -> Maybe (List (WithBounds VToken))
lexViolet str =
  case lex violetTokenMap str of
    (tokens, _, _, "") => Just tokens
    _ => Nothing
