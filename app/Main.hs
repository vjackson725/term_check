{-# LANGUAGE LambdaCase, ScopedTypeVariables, TupleSections #-}

import Data.Foldable
import Data.List
import Options.Applicative
import System.Exit
import System.IO

import qualified Data.Map as M

import TerminationChecking.Exec
import TerminationChecking.Lang
import TerminationChecking.Parser (Prog, parse_program)
import TerminationChecking.Solver (TermResult, solve_mat)

import qualified Data.Map as M

pretty_matrix :: [[Entry]] -> String
pretty_matrix m =
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

make_matrix_cmd :: Parser Command
make_matrix_cmd =
  (, PhProgText, PhMatrix) <$> argument str (metavar "FILENM")

matrix_check_cmd :: Parser Command
matrix_check_cmd =
  (, PhMatrix, PhSoln) <$> argument str (metavar "MATRIX")

program_check_cmd :: Parser Command
program_check_cmd =
  (, PhProgText, PhSoln) <$> argument str (metavar "FILENM")

termcheck_argparser :: ParserInfo Command
termcheck_argparser =
  info
    (subparser
      (  command "makematrix" (info make_matrix_cmd (progDesc "Make a matrix from a program"))
      <> command "matrixcheck" (info matrix_check_cmd (progDesc "Check a matrix is solvable"))
      <> command "programcheck" (info program_check_cmd (progDesc "Check a program terminates"))
      <> command "solve" (info program_check_cmd (progDesc "Check a program terminates"))
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
      (hPutStr stderr $ "ERROR: " ++ err ++ "\n") >>
      exitWith (ExitFailure 1)
    Right prog -> return . PhDatProgram $ prog
phaseStep (PhDatProgram prog) =
  return . PhDatMatrix $
    M.mapWithKey (\k v -> matrixify k v) prog
phaseStep (PhDatMatrix mat) =
  return . PhDatSoln $ M.map solve_mat mat

main :: IO ()
main =
  do
    (filenm, startPhase, endPhase) <- customExecParser p termcheck_argparser
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
          (hPutStr stderr $ "ERROR: can't start in solution phase\n") >>
          exitWith (ExitFailure 1)
    -- Run program
    result <- doUntil (isPhase endPhase) phaseStep phin
    -- Output results
    _ <-
      case result of
        PhDatProgText progtext ->
          (hPutStr stderr $ "ERROR: can't end in read file phase\n") >>
          exitWith (ExitFailure 1)
        PhDatProgram prog ->
          putStrLn $ show prog
        PhDatMatrix mats ->
          traverse_
            (\(fnnm, mat) ->
              putStrLn (fnnm ++ ": " ++ pretty_matrix mat) >> return ())
            (M.toAscList mats)
        PhDatSoln res ->
          putStrLn . show $ res
    return ()
  where
    p = prefs showHelpOnError
