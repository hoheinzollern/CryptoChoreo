{-# LANGUAGE ScopedTypeVariables #-}

module TestRunner 
  ( runProVerifTest
  , runProVerifTests
  , TestResult(..)
  , TestSummary(..)
  , summarizeTests
  , showTestResult
  , showTestSummary
  ) where

import ProVerifResult
import System.Process
import System.Exit
import Control.Exception (try, SomeException)

-- | Result of running ProVerif on a single file
data TestResult = TestResult
  { testFile :: FilePath
  , testSuccess :: Bool
  , testQueries :: [QueryResult]
  , testError :: Maybe String
  } deriving (Show)

-- | Summary of multiple test results
data TestSummary = TestSummary
  { totalTests :: Int
  , passedTests :: Int
  , failedTests :: Int
  , errorTests :: Int
  } deriving (Show)

-- | Run ProVerif on a single file and parse results
runProVerifTest :: FilePath -> IO TestResult
runProVerifTest file = do
  result <- try $ readProcess "proverif" [file] ""
  case result of
    Left (e :: SomeException) -> 
      return $ TestResult
        { testFile = file
        , testSuccess = False
        , testQueries = []
        , testError = Just (show e)
        }
    Right output -> do
      let pvOutput = parseProVerifOutput output
      let success = allQueriesTrue (queries pvOutput)
      return $ TestResult
        { testFile = file
        , testSuccess = success
        , testQueries = queries pvOutput
        , testError = Nothing
        }

-- | Run ProVerif on multiple files
runProVerifTests :: [FilePath] -> IO [TestResult]
runProVerifTests = mapM runProVerifTest

-- | Compute summary from test results
summarizeTests :: [TestResult] -> TestSummary
summarizeTests results = TestSummary
  { totalTests = length results
  , passedTests = length [r | r <- results, testSuccess r, testError r == Nothing]
  , failedTests = length [r | r <- results, not (testSuccess r), testError r == Nothing]
  , errorTests = length [r | r <- results, testError r /= Nothing]
  }

-- | Pretty print a test result
showTestResult :: TestResult -> String
showTestResult tr = unlines $
  [ "File: " ++ testFile tr
  , "Status: " ++ if testSuccess tr then "PASS" else "FAIL"
  ] ++
  (case testError tr of
    Just err -> ["Error: " ++ err]
    Nothing -> map (("  " ++) . showQueryResult) (testQueries tr))

-- | Pretty print test summary
showTestSummary :: TestSummary -> String
showTestSummary ts = unlines
  [ "========================================="
  , "Test Summary:"
  , "  Total: " ++ show (totalTests ts)
  , "  Passed: " ++ show (passedTests ts)
  , "  Failed: " ++ show (failedTests ts)
  , "  Errors: " ++ show (errorTests ts)
  , "========================================="
  ]
