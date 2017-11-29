module Main where

import System.Exit
import System.Process
import System.Directory

main :: IO ExitCode
main =
  withCurrentDirectory sourceDir $
  mconcat <$>
  mapM runLiquid orderedFiles

orderedFiles :: [FilePath]
orderedFiles =
  [ "Proofs.hs"
  , "Replicate.hs"
  , "Flatten.hs"
  , "ReverseEfficient.hs"
  , "AdditionCompiler.hs"
  , "Exercises.hs"
  , "Types.hs"
  , "Data/List/Verified.hs"
  , "Data/Monoid/Verified.hs"
  ]

sourceDir :: FilePath
sourceDir = "src"

runLiquid :: FilePath -> IO ExitCode
runLiquid file = spawnProcess "stack" args >>= waitForProcess
  where args = ["exec", "--", "liquid", file]

instance Monoid ExitCode where
  mempty = ExitSuccess
  mappend (ExitFailure i) _ = ExitFailure i 
  mappend ExitSuccess e = e
