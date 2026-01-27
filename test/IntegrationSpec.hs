{-# LANGUAGE ScopedTypeVariables #-}

module IntegrationSpec (spec) where

import Test.Hspec
import ProVerifResult
import System.Process
import System.Exit
import System.Directory
import System.FilePath
import Control.Exception (try, SomeException)
import Control.Monad (when, forM_)
import Data.List (isSuffixOf)

-- | Files to exclude from testing (e.g., too slow to verify)
excludedFiles :: [String]
excludedFiles = 
  [ "SSO-DH.choreo"  -- Takes too long to verify
  ]


-- | Run CCHaskell with ProVerif on a choreography file
runCCHaskellWithProVerif :: FilePath -> IO (Either String ProVerifOutput)
runCCHaskellWithProVerif choreoFile = do
  let outputPV = "pvs/test-output.pv"
  result <- try $ do
    -- Run CCHaskell to generate ProVerif file and execute it
    (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" 
      [ "run", "CCHaskell", "--"
      , "--pvout", outputPV
      , "--runproverif"
      , choreoFile
      ] ""
    
    -- Clean up the generated PV file
    exists <- doesFileExist outputPV
    when exists $ removeFile outputPV
    
    case exitCode of
      ExitSuccess -> return $ parseProVerifOutput stdout
      ExitFailure _ -> error $ "CCHaskell failed: " ++ stderr
  
  case result of
    Left (e :: SomeException) -> return $ Left (show e)
    Right pvOutput -> return $ Right pvOutput

-- | Run CCHaskell with ProVerif using --stitch for API verification
runCCHaskellWithStitch :: String -> IO (Either String ProVerifOutput)
runCCHaskellWithStitch stitchSpec = do
  let outputPV = "pvs/test-output.pv"
  result <- try $ do
    -- Run CCHaskell to generate ProVerif file and execute it with stitching
    (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" 
      [ "run", "CCHaskell", "--"
      , "--pvout", outputPV
      , "--runproverif"
      , "--stitch", stitchSpec
      ] ""
    
    -- Clean up the generated PV file
    exists <- doesFileExist outputPV
    when exists $ removeFile outputPV
    
    case exitCode of
      ExitSuccess -> return $ parseProVerifOutput stdout
      ExitFailure _ -> error $ "CCHaskell failed: " ++ stderr
  
  case result of
    Left (e :: SomeException) -> return $ Left (show e)
    Right pvOutput -> return $ Right pvOutput


-- | Get all top-level .choreo files from examples directory
getExampleFiles :: IO [FilePath]
getExampleFiles = do
  files <- listDirectory "examples"
  let choreoFiles = filter (".choreo" `isSuffixOf`) files
  let filtered = filter (\f -> f `notElem` excludedFiles) choreoFiles
  return $ map ("examples" </>) filtered

-- | Get all .choreo files from examples/negatives directory
getNegativeExampleFiles :: IO [FilePath]
getNegativeExampleFiles = do
  let negativesDir = "examples/negatives"
  exists <- doesDirectoryExist negativesDir
  if not exists
    then return []
    else do
      files <- listDirectory negativesDir
      let choreoFiles = filter (".choreo" `isSuffixOf`) files
      return $ map (negativesDir </>) choreoFiles

-- | Check if no queries are true (all should be false or cannot be proved)
noQueriesTrue :: [QueryResult] -> Bool
noQueriesTrue = all (not . isQueryTrue)
  where
    isQueryTrue (QueryTrue _) = True
    isQueryTrue _ = False

-- | API test cases with stitch specifications
-- Format: (description, stitchSpec)
apiTestCases :: [(String, String)]
apiTestCases =
  [ ("ASW with ttp API", "./examples/ASW.choreo:main,O,R;./examples/APIs/ASW-API.choreo:ttp")
  , ("chat-server with ttp API", "./examples/chat-server.choreo:main,A,B;./examples/APIs/chat-server-API.choreo:ttp")
  , ("NSLPK with server API", "./examples/NSLPK.choreo:main,A,B;./examples/APIs/NSLPK-API.choreo:s")
  , ("SSO-simple with ttp API", "./examples/SSO-simple.choreo:main,A,B;./examples/APIs/SSO-simple-API.choreo:ttp")
  , ("tpm-simple with tpm API", "./examples/tpm-simple.choreo:main,alice,Parent;./examples/APIs/tpm-simple-API.choreo:tpm")
  , ("declassify-or-delete with a API", "./examples/declassify-or-delete.choreo:main,b;./examples/APIs/declassify-or-delete-API.choreo:a")
  , ("SSO-DH with a API", "./examples/SSO-DH.choreo:main,A,B;./examples/APIs/SSO-DH-API.choreo:ttp")
  ]

spec :: Spec
spec = describe "ProVerif Integration Tests" $ do
  
  describe "All example protocols" $ do
    exampleFiles <- runIO getExampleFiles
    
    forM_ exampleFiles $ \file -> 
      it ("should verify all queries in " ++ takeFileName file) $ do
        result <- runCCHaskellWithProVerif file
        case result of
          Left err -> expectationFailure $ "Failed to run: " ++ err
          Right pvOutput -> do
            let qs = queries pvOutput
            qs `shouldSatisfy` (not . null)
            allQueriesTrue qs `shouldBe` True
  
  describe "Negative examples (should not verify)" $ do
    negativeFiles <- runIO getNegativeExampleFiles
    
    forM_ negativeFiles $ \file -> 
      it ("should have no true queries in " ++ takeFileName file) $ do
        result <- runCCHaskellWithProVerif file
        case result of
          Left err -> expectationFailure $ "Failed to run: " ++ err
          Right pvOutput -> do
            let qs = queries pvOutput
            qs `shouldSatisfy` (not . null)
            noQueriesTrue qs `shouldBe` True
  
  describe "API verification with stitching" $ do
    forM_ apiTestCases $ \(description, stitchSpec) ->
      it ("should verify " ++ description) $ do
        result <- runCCHaskellWithStitch stitchSpec
        case result of
          Left err -> expectationFailure $ "Failed to run: " ++ err
          Right pvOutput -> do
            let qs = queries pvOutput
            qs `shouldSatisfy` (not . null)
            allQueriesTrue qs `shouldBe` True

-- | Test a single protocol file
testProtocol :: FilePath -> IO (FilePath, Bool)
testProtocol file = do
  putStrLn $ "Testing: " ++ file
  result <- runCCHaskellWithProVerif file
  case result of
    Left err -> do
      putStrLn $ "  ERROR: " ++ err
      return (file, False)
    Right pvOutput -> do
      let qs = queries pvOutput
      let success = allQueriesTrue qs
      if success
        then putStrLn $ "  ✓ PASS (" ++ show (length qs) ++ " queries)"
        else putStrLn $ "  ✗ FAIL - some queries failed"
      return (file, success)
