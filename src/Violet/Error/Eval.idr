module Violet.Error.Eval

import Violet.Core.Term
import Text.PrettyPrint.Prettyprinter.Doc
import Text.PrettyPrint.Prettyprinter.Render.Terminal
import Violet.Error.Common

public export
data EvalError
	= NoVar String
	| BadSpine Tm
	| OutOfCase

export
prettyEvalError : EvalError -> Doc AnsiStyle
prettyEvalError (NoVar name) = annBold $ annColor Red $ hsep ["variable:", pretty name, "not found"]
prettyEvalError (BadSpine tm) = annBold $ annColor Red $ hsep ["bad spine on:", pretty tm]
prettyEvalError OutOfCase = annBold $ annColor Red $ "pattern matching out of case"
