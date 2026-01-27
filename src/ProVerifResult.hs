{-# LANGUAGE OverloadedStrings #-}

{-# LANGUAGE OverloadedStrings #-}

module ProVerifResult 
  ( QueryResult(..)
  , ProVerifOutput(..)
  , parseProVerifOutput
  , parseQueryResults
  , showQueryResult
  , countResults
  , allQueriesTrue
  , resultSummary
  , extractResultLines
  , simpleParseResults
  ) where

import Text.Parsec
import Text.Parsec.String (Parser)
import Data.List (isPrefixOf, isInfixOf)

-- | Represents the result of a ProVerif query
data QueryResult 
  = QueryTrue String      -- ^ Query is true with the query text
  | QueryFalse String     -- ^ Query is false (attack found) with the query text
  | QueryCannotProve String -- ^ Query cannot be proven with the query text
  deriving (Eq, Show)

-- | Represents the complete ProVerif output with all query results
data ProVerifOutput = ProVerifOutput
  { queries :: [QueryResult]
  , rawOutput :: String
  } deriving (Eq, Show)

-- | Parse a single RESULT line from ProVerif output
parseResultLine :: Parser QueryResult
parseResultLine = do
  _ <- string "RESULT "
  queryText <- manyTill anyChar (try (string " is "))
  result <- choice 
    [ string "true." >> return (QueryTrue queryText)
    , string "false." >> return (QueryFalse queryText)
    , string "cannot be proved." >> return (QueryCannotProve queryText)
    , string "cannot be proved" >> return (QueryCannotProve queryText)
    ]
  optional (char '\n')
  return result

-- | Parse all RESULT lines from ProVerif output
parseQueryResults :: String -> Either ParseError [QueryResult]
parseQueryResults input = 
  parse (many (try parseWithSkip)) "" input
  where
    parseWithSkip :: Parser QueryResult
    parseWithSkip = do
      _ <- manyTill anyChar (try (lookAhead (string "RESULT ")))
      parseResultLine

-- | Parse complete ProVerif output
parseProVerifOutput :: String -> ProVerifOutput
parseProVerifOutput output = 
  ProVerifOutput 
    { queries = case parseQueryResults output of
                  Right qs -> qs
                  Left _   -> []
    , rawOutput = output
    }

-- | Extract just the RESULT lines from raw output (alternative simple approach)
extractResultLines :: String -> [String]
extractResultLines = filter ("RESULT " `isPrefixOf`) . lines

-- | Simple parser that extracts results without full parsing
simpleParseResults :: String -> [QueryResult]
simpleParseResults output = 
  map parseSimpleLine (extractResultLines output)
  where
    parseSimpleLine :: String -> QueryResult
    parseSimpleLine line 
      | " is true." `isInfixOf` line = 
          QueryTrue (extractQuery line)
      | " is false." `isInfixOf` line = 
          QueryFalse (extractQuery line)
      | " cannot be proved" `isInfixOf` line = 
          QueryCannotProve (extractQuery line)
      | otherwise = 
          QueryCannotProve (extractQuery line)  -- default fallback
    
    extractQuery :: String -> String
    extractQuery line = 
      let afterResult = drop 7 line  -- drop "RESULT "
          parts = words afterResult
          beforeIs = unwords $ takeWhile (/= "is") parts
      in beforeIs

-- | Pretty print a query result
showQueryResult :: QueryResult -> String
showQueryResult (QueryTrue q) = "✓ TRUE: " ++ q
showQueryResult (QueryFalse q) = "✗ FALSE: " ++ q
showQueryResult (QueryCannotProve q) = "? CANNOT PROVE: " ++ q

-- | Count results by type
countResults :: [QueryResult] -> (Int, Int, Int)
countResults results = 
  ( length [() | QueryTrue _ <- results]
  , length [() | QueryFalse _ <- results]
  , length [() | QueryCannotProve _ <- results]
  )

-- | Check if all queries passed (are true)
allQueriesTrue :: [QueryResult] -> Bool
allQueriesTrue = all isTrue
  where
    isTrue (QueryTrue _) = True
    isTrue _ = False

-- | Get summary of results
resultSummary :: [QueryResult] -> String
resultSummary results = 
  let (trueCount, falseCount, cannotProveCount) = countResults results
      total = length results
  in unlines
    [ "ProVerif Results:"
    , "  Total queries: " ++ show total
    , "  True: " ++ show trueCount
    , "  False: " ++ show falseCount
    , "  Cannot prove: " ++ show cannotProveCount
    , "  Success: " ++ if allQueriesTrue results then "YES" else "NO"
    ]
