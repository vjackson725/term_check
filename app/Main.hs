{-# LANGUAGE LambdaCase, ScopedTypeVariables, TupleSections #-}

import Control.Monad (void)
import Data.Foldable
import Data.List
import Options.Applicative
import System.Exit
import System.IO

import qualified Data.Map as M

import TerminationChecking.Exec
import TerminationChecking.Lang
import TerminationChecking.Parser (Prog, parse_program)
import TerminationChecking.Solver --(TermResult, solve_mat)

prettyMatrix :: [[Entry]] -> String
prettyMatrix m =
  let lvl2 :: [[String]] = map (map (\case { Sym s -> "?"; Num n -> show n })) m
      lvl1 :: [String] =  map (('[' :) . foldr (++) "]" . intersperse ", ") lvl2
      lvl0 :: String =  ('[' :) . foldr (++) "]" . intersperse ", " $ lvl1
    in lvl0

--
-- Compiler Phase and Phase Data
--

data Phase = PhProgText | PhProgram | PhMatrix | PhSoln
  deriving (Show, Eq, Ord)

data PhaseData =
  PhDatProgText String |
  PhDatProgram Prog |
  PhDatMatrix (M.Map String [[Entry]]) |
  PhDatSoln (M.Map String TermResult)
  deriving (Show, Eq)

isPhase :: Phase -> PhaseData -> Bool
isPhase PhProgText  PhDatProgText{} = True
isPhase PhProgram   PhDatProgram{}  = True
isPhase PhMatrix    PhDatMatrix{}   = True
isPhase PhSoln      PhDatSoln{}     = True
isPhase _ _ = False

--
-- Program command-line commands
--

type Command = (String, Phase, Phase)

makeMatrixCmd :: Parser Command
makeMatrixCmd =
  (, PhProgText, PhMatrix) <$> argument str (metavar "FILENM")

matrixCheckCmd :: Parser Command
matrixCheckCmd =
  (, PhMatrix, PhSoln) <$> argument str (metavar "MATRIX")

programCheckCmd :: Parser Command
programCheckCmd =
  (, PhProgText, PhSoln) <$> argument str (metavar "FILENM")

termcheckArgparser :: ParserInfo Command
termcheckArgparser =
  info
    (subparser
      (  command "makematrix" (info makeMatrixCmd (progDesc "Make a matrix from a program"))
      <> command "matrixcheck" (info matrixCheckCmd (progDesc "Check a matrix is solvable"))
      <> command "programcheck" (info programCheckCmd (progDesc "Check a program terminates"))
      <> command "solve" (info programCheckCmd (progDesc "Check a program terminates"))
      ) <**> helper)
    (progDesc "Linear-Lexicographic program termination checker.")

--
-- Main Program
--

doUntil :: Monad m => (a -> Bool) -> (a -> m a) -> a -> m a
doUntil p stepfn a =
  if p a
    then return a
    else
      do
        a' <- stepfn a
        doUntil p stepfn a'

phaseStep :: PhaseData -> IO PhaseData
phaseStep (PhDatProgText progText) =
  case parse_program progText of
    Left err ->
      hPutStr stderr ("ERROR: " ++ err ++ "\n") >>
      exitWith (ExitFailure 1)
    Right prog -> return . PhDatProgram $ prog
phaseStep (PhDatProgram prog) =
  return . PhDatMatrix $
    M.mapWithKey matrixify prog
phaseStep (PhDatMatrix mat) =
  return . PhDatSoln $ M.map solveMat mat

main :: IO ()
main =
  do
    (filenm, startPhase, endPhase) <- customExecParser p termcheckArgparser
    -- Read file
    filetext <- readFile filenm
    -- Create start phase data
    phin <-
      case startPhase of 
        PhProgText -> return $ PhDatProgText filetext
        PhProgram  ->
          -- TODO: filetext to abstract program
          error "ERROR: abstract program phase start not implemented yet"
        PhMatrix   ->
          -- TODO: filetext to matrix
          error "ERROR: matrix phase start not implemented yet\n"
        PhSoln     ->
          hPutStr stderr "ERROR: can't start in solution phase\n" >>
          exitWith (ExitFailure 1)
    -- Run program
    result <- doUntil (isPhase endPhase) phaseStep phin
    -- Output results
    _ <-
      case result of
        PhDatProgText progtext ->
          hPutStr stderr "ERROR: can't end in read file phase\n" >>
          exitWith (ExitFailure 1)
        PhDatProgram prog ->
          print prog
        PhDatMatrix mats ->
          traverse_
            (\(fnnm, mat) ->
              void $ putStrLn (fnnm ++ ": " ++ prettyMatrix mat))
            (M.toAscList mats)
        PhDatSoln res ->
          print res
    return ()
  where
    p = prefs showHelpOnError
