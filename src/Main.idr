module Main

import System
import Control.App
import Control.App.Console
import Control.App.FileIO
import Data.String
import Text.PrettyPrint.Prettyprinter.Doc
import Text.PrettyPrint.Prettyprinter.Render.Terminal

import Violet.Core
import Violet.Syntax
import Violet.Parser

export
handle : (PrimIO es, FileIO (IOError :: es), Console es) => List String -> App es ()
handle [_, "check", filename] =
  handle (readFile filename)
    (\source =>
      case (parse source) of
        Left pErr => primIO $ putDoc $ prettyError pErr
        Right raw =>
          let tm = (toTm raw)
          in case (infer emptyEnv emptyCtx tm) of
            Left cErr => primIO $ putDoc $
              (annotate bold $ pretty (nf0 tm))
              <++> "has error:"
              <++> line
              <++> prettyCheckError filename source cErr
            Right vty => primIO $ putDoc $
              (annotate bold $ pretty (nf0 tm))
              <++> ":"
              <++> (annotate bold $ annotate (color Blue) $ pretty (quote emptyEnv vty))
      )
    (\err : IOError => putStrLn $ "error: " ++ show err)
handle _ = pure ()

main : IO ()
main = run $ handle !getArgs
