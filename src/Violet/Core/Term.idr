module Violet.Core.Term

import Data.String
import public Text.Bounded
import Text.PrettyPrint.Prettyprinter.Doc
import Text.PrettyPrint.Prettyprinter.Symbols
import Text.PrettyPrint.Prettyprinter.Render.Terminal

public export
Name : Type
Name = String

public export
data Pat
  = PVar Name
  | PCons Name (List Name)

mutual
  ||| The Core Term of violet language
  public export
  data Tm
    = SrcPos (WithBounds Tm)
    | Var Name             -- x
    | Lam Name Tm          -- λ x => t
    | Apply Tm Tm          -- t u
    | U                    -- U
    | Pi Name Ty Ty        -- (x : a) → b
    | Let Name Ty Tm Tm    -- let x : a = t; u
    | Elim Tm (List (Pat, Tm))
    -- FIXME?: maybe constructor should be treated special
    | Postulate Name Ty Tm -- posulate x : a; u
    -- data
    | Sum Name (List (Name, List Ty))
    | Intro Name Ty Tm

  public export
  Ty : Type
  Ty = Tm

export
Pretty Pat where
  pretty (PVar n) = pretty n
  pretty (PCons h vs) = pretty h <++> hsep (map pretty vs)

export
Pretty Tm where
  pretty (SrcPos t) = pretty t.val
  pretty (Var name) = pretty name
  pretty (Lam x t) = hsep ["λ", pretty x, "=>", pretty t]
  pretty (Apply t u) = pretty t <++> case u of
    SrcPos t => parens $ pretty t.val
    Apply {}   => parens $ pretty u
    _        => pretty u
  pretty U = "U"
  pretty (Pi x a b) =
    hsep [ hcat ["(", pretty x],
           ":",
           hcat [pretty a, ")"],
           "→", pretty b
         ]
  pretty (Let x a t u) =
    hsep [ "let", pretty x, ":", pretty a, "=", hcat [pretty t, ";"] ]
    <++> line
    <++> pretty u
  pretty (Elim tm cases) =
    "elim" <++> pretty tm
    <++> line
    <++> vsep (map prettyCase cases)
    where
      prettyCase : (Pat, Tm) -> Doc ann
      prettyCase (p, t) = pipe <++> pretty p <++> "=>" <++> pretty tm
  pretty (Postulate x a u) =
    hsep ["postulate", pretty x, ":", hcat [pretty a, ";"]]
    <++> line
    <++> pretty u
  pretty (Intro x t u) = spaces 2 <++> hsep ["constructor", pretty x] <++> line <++> pretty u
  pretty (Sum x cases) = vsep (hsep ["data", pretty x] :: map pp cases)
  where
    pp : (Name, List Ty) -> Doc ann
    pp (x, ts) = "|" <++> pretty x <++> hsep (map pretty ts)
