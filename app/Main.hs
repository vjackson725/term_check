{-# LANGUAGE LambdaCase, ScopedTypeVariables, TupleSections #-}

import Debug.Trace

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
import TerminationChecking.Solver
import TerminationChecking.Misc

import Text.Printf (printf)

prettyMatrix :: [[Entry]] -> String
prettyMatrix m =
  let lvl2 :: [[String]] = map (map (\case { Inf -> "ω"; Num n -> show (fromRational n) })) m
      colWidth = map (foldr (\x y -> max (length x) y) (0 :: Int)) $ transpose lvl2
      lvl1 :: [String] =
        map
          (\row ->
            let row2 =
                  map
                    (\(i,x) ->
                      let width = colWidth !! i
                      in replicate (width - length x) ' ' ++ x)
                    (enumerate row)
                row3 = concat (intersperse ", " $ row2)
            in '[' : row3 ++ "]")
          lvl2
      lvl0 :: String =  foldr (++) "" . intersperse "\n" $ lvl1
    in lvl0

--
-- Compiler Phase and Phase Data
--

data Phase = PhProgText | PhProgram | PhMeasures | PhMatrix | PhSoln
  deriving (Show, Eq, Ord)

data PhaseData =
  PhDatProgText String |
  PhDatProgram Prog |
  PhDatMeasures Prog |
  PhDatMatrix (M.Map String ([Measure], [[Entry]])) |
  PhDatSoln (M.Map String (TermResult String))
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
      (  command "makematrix" (info makeMatrixCmd (progDesc "Print the primitive measure and termination matrix for every function in a program"))
      <> command "programcheck" (info programCheckCmd (progDesc "Check a program terminates"))
      <> command "solve" (info programCheckCmd (progDesc "Check a program terminates (alias of programcheck)"))
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

{-
  There are three steps this program can perform:
    1. (PhDatProgText) Transform program text into a Prog (a collection of
       named function definitions).
    2. (PhDatProgram) Transform a Prog into an Entry matrix (a matrix where
       the rows correspond to recursive calls, and the columns  to measures).
    3. (PhDatMatrix) Solve the termination problem specified by an entry matrix.
-}
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
phaseStep (PhDatMatrix fnMeasAndMat) =
  -- TODO: fix duplication of measure name logic
  let soln = M.map
              (\(meas, mat) ->
                solveMat ((map (\n -> 'm' : show n) [0..max 0 (length meas-1)])) mat)
              fnMeasAndMat
   in return $ PhDatSoln soln

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
          error "ERROR: Start from abstract program not implemented\n"
        PhMatrix   ->
          -- TODO: filetext to matrix
          error "ERROR: Start from matrix not implemented\n"
        PhSoln     ->
          hPutStr stderr "Internal Error: can't start in solution phase\n" >>
          exitWith (ExitFailure 1)
    -- Run program
    result <- doUntil (isPhase endPhase) phaseStep phin
    -- Output results
    _ <-
      case result of
        PhDatProgText progtext ->
          hPutStr stderr "Internal Error: can't end in read file phase\n" >>
          exitWith (ExitFailure 1)
        PhDatProgram prog ->
          print prog
        PhDatMatrix fnMeasAndMat ->
          traverse_
            (\(fnnm, (meas, mat)) ->
              do
                let measNames = (map (\n -> 'm' : show n) [0..max 0 (length meas-1)])
                _ <- putStrLn ("== Fun: " ++ fnnm ++ " ==")
                _ <- putStr (intercalate "\n" $ map
                                                  (\(n,(fp, fr)) ->
                                                    let rpart = intercalate " <| " . map show . reverse $ fr
                                                        ppart = intercalate " <| " . map show . reverse $ fp
                                                     in if null fp then
                                                          fmtFixOnly n rpart
                                                        else if null fr then
                                                          fmtPathOnly n ppart
                                                        else
                                                          fmtMeasure n rpart ppart) $
                                                  zip measNames meas)
                _ <- if null mat
                      then putStrLn "\n[]"
                      else putStrLn "\n" >> putStrLn (prettyMatrix mat)
                _ <- putStrLn ""
                return ())
            (M.toAscList fnMeasAndMat)
        PhDatSoln fnress ->
          traverse_
            (\(fnnm, mres) ->
              putStrLn ("== Fun: " ++ fnnm ++ " ==") >>
              (case mres of
                Nothing ->
                  putStrLn "Failed to show termination"
                Just res ->
                  putStrLn "Found termination measure:" >>
                  putStr "  " >>
                  putStrLn ("[" ++ intercalate ", " (map (intercalate " + " . map (\(k,m) -> show k ++ "*" ++ m)) res) ++ "]")) >>
              putStrLn "")
            (M.toAscList fnress)
    return ()
  where
    p = prefs showHelpOnError
    fmtFixOnly  = printf "%s: fix (%s)"
    fmtPathOnly = printf "%s: %s"
    fmtMeasure  = printf "%s: fix (%s) <| (%s)"