{-# LANGUAGE OverloadedStrings, NoImplicitPrelude #-}


module SEDEL
  ( evalFile
  , readAndEval
  , driver
  , render
  ) where

import           Control.Exception (SomeException, try)
import qualified Data.Text as T
import           Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Protolude hiding (evaluate)

import           SEDEL.Environment
import           SEDEL.Parser.Parser (parseModule)
import           SEDEL.PrettyPrint
import           SEDEL.Source.Syntax
import           SEDEL.Source.Inference
import           SEDEL.Target.Eval

type Result = Either FDoc (Scheme, Text)

parseExpectedOutput :: Text -> Maybe Text
parseExpectedOutput source =
  let firstLine = T.takeWhile (/= '\n') source
  in fmap T.strip (T.stripPrefix "-->" (T.strip firstLine))

readTry :: IO Text -> IO (Either SomeException Text)
readTry = try

driver :: SCtx -> Module -> IO Result
driver ctx abt = do
  res <- runTcMonad ctx (tcModule abt)
  case res of
    Right (typ, tar) -> do
      r <- evaluate tar
      case r of
        Right eres -> return $ Right (typ, show eres)
        Left er -> return $ Left (Pretty.pretty er)
    Left er -> return (Left (pprint er))


render :: (Scheme, Text) -> FDoc
render (ty, res) =
  "Typing result" <> Pretty.line <> Pretty.colon <+>
  pprint ty <> Pretty.line <> Pretty.line <> "Evaluation result" <> Pretty.line <> "=>" <+>
  Pretty.pretty res


readAndEval :: FilePath -> IO FDoc
readAndEval path = do
  msg <- readTry $ readFile path
  case msg of
    Left err -> return $ "Load file error" <+> Pretty.pretty (T.pack (show err))
    Right contents ->
      case parseModule (toS contents) of
        Left err -> return $ "Syntax error" <+> Pretty.pretty err
        Right abt -> do
          res <- driver emptyCtx abt
          case res of
            Left err -> return err
            Right r -> return (render r)


-- For test purposes
evalFile :: FilePath -> IO ((FDoc, Maybe FDoc), Bool)
evalFile path = do
  msg <- readTry $ readFile path
  let failed d = return ((d, Nothing), False)
      failWith d d' = return ((d, Just d'), False)
      succeed d = return ((d, Nothing), True)
  case msg of
    Left err -> failed $ "Load file error" <+> Pretty.pretty (T.pack (show err))
    Right contents ->
      case parseModule (toS contents) of
        Left err -> failed (Pretty.pretty err)
        Right abt -> do
          value <- driver emptyCtx abt
          case value of
            Left err -> failed err
            Right (_, tm) ->
              case parseExpectedOutput contents of
                Nothing -> failed $ "No expectation" <+> Pretty.pretty tm
                Just expinp ->
                  if tm == expinp
                    then succeed (Pretty.pretty tm)
                    else failWith (Pretty.pretty tm) (Pretty.pretty expinp)
