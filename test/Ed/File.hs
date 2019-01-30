{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
module Ed.File (prop_ed_blackbox_file) where

import           Prelude           hiding (FilePath)

import           Control.Lens      (snoc, (^?), ix)

import           Data.Bifoldable   (bifold)
import           Data.Bifunctor    (first, second)

import qualified Data.Text         as T
import qualified Data.Text.IO      as T

import           Hedgehog
import qualified Hedgehog.Gen      as Gen
import qualified Hedgehog.Range    as Range

import           Ed.Types          (Buffer (..), Cmd_Append (..),
                                    Cmd_AppendAt (..), Cmd_DeleteLine (..),
                                    Cmd_PrintAll (..), Cmd_JoinLines (..),
                                    getBufferLength, getTextLength)

import           Turtle
import           Turtle.Format     (d, format, (%))

import           System.Posix.Temp (mkstemp)

resetEdFile :: FilePath -> IO ()
resetEdFile edFile = sh $
  testfile edFile
  >>= (`when` (rm edFile))
  >> touch edFile

edCmdsOnFile :: FilePath -> [Text] -> IO ()
edCmdsOnFile edFile = sh .
  procs "ed" ["-s", format fp edFile]
  . select
  . textToLines
  . T.unlines

readEdFile :: FilePath -> IO Text
readEdFile edFile = T.readFile (T.unpack $ format fp edFile)

genLineNum :: MonadGen m => Buffer v -> m Word
genLineNum b = Gen.word (Range.linear 1 (getBufferLength b))

genTextInp :: MonadGen m => m Text
genTextInp = Gen.text (Range.linear 1 100) Gen.alphaNum

cAppendAt
  :: ( MonadGen n
     , MonadIO m
     , MonadTest m
     )
  => FilePath
  -> Command n m Buffer
cAppendAt edFile =
  let
    gen b = Just $
      Cmd_AppendAt <$> genLineNum b <*> genTextInp

    execute (Cmd_AppendAt ln i) = evalIO $
      edCmdsOnFile edFile
        [ format (d%"a") ln
        , i
        , "."
        , "w"
        , "q"
        ]
      >> readEdFile edFile
  in
    Command gen execute
    [ Require $ \(Buffer b) (Cmd_AppendAt ln _) ->
        ln >= 0 && ln < fromIntegral (length b) && not (null b)

    , Update $ \(Buffer b) (Cmd_AppendAt ln i) _ ->
        Buffer
        . bifold
        . second (i:)
        . splitAt (fromIntegral ln) $ b

    , Ensure $ \(Buffer _old) (Buffer new) (Cmd_AppendAt ln i) out -> do
        T.unlines new === out
        -- Can't get here without having perfomed a valid insert, so totes safe, right?...RIGHT!?
        new !! (fromIntegral ln) === i
    ]

cAppendText
  :: ( MonadGen n
     , MonadIO m
     , MonadTest m
     )
  => FilePath
  -> Command n m Buffer
cAppendText edFile =
  let
    gen _ = Just $ Cmd_Append <$> genTextInp

    execute (Cmd_Append t) = evalIO $
      edCmdsOnFile edFile
        [ "a"
        , t
        , "."
        , "w"
        , "q"
        ]
      >> readEdFile edFile

  in
    Command gen execute
    [ Update $ \(Buffer b) (Cmd_Append i) _ -> Buffer (snoc b i)
    , Ensure $ \_ (Buffer new) _ out        -> T.unlines new === out
    ]

cPrintAll
  :: ( MonadIO m
     , MonadTest m
     , MonadGen n
     )
  => FilePath
  -> Command n m Buffer
cPrintAll edFile =
  let
    gen _ = Just $ Gen.constant Cmd_PrintAll

    execute _ = evalIO $ readEdFile edFile

  in
    Command gen execute
    [ Require $ \(Buffer cur) _                  -> not $ null cur
    , Ensure  $ \(Buffer old) (Buffer new) _ _   -> old === new
    , Ensure  $ \_            (Buffer new) _ out -> out === T.unlines new
    ]

cDeleteLine
  :: ( MonadIO m
     , MonadTest m
     , MonadGen n
     )
  => FilePath
  -> Command n m Buffer
cDeleteLine edFile =
  let
    gen b = Just $
      Cmd_DeleteLine <$> genLineNum b

    execute (Cmd_DeleteLine n) = evalIO $ do
      edCmdsOnFile edFile
        [ format (d%"d") n
        , "w"
        , "q"
        ]
      readEdFile edFile
  in
    Command gen execute
    [ Require $ \(Buffer b) (Cmd_DeleteLine n) ->
        n >= 0 && n < fromIntegral (length b) && not (null b)

    , Update $ \(Buffer b) (Cmd_DeleteLine n) _ ->
        Buffer
        . bifold
        . first (take (fromIntegral n - 1))
        $ splitAt (fromIntegral n) b

    , Ensure $ \(Buffer old) (Buffer new) (Cmd_DeleteLine n) out -> do
        T.unlines new === out
        let n' = fromIntegral n
        new ^? ix n'       === old ^? ix (n' + 1)
        new ^? ix (n' - 1) === old ^? ix n'
    ]

-- Joins the addressed lines, replacing them by a single line containing their joined text.
-- If only one address is given, this command does nothing.
-- If lines are joined, the current address is set to the address of the joined line.
-- Else, the current address is unchanged.
cJoinLines
  :: ( MonadGen n
     , MonadIO m
     , MonadTest m
     )
  => FilePath
  -> Command n m Buffer
cJoinLines edFile =
  let
    gen b = Just $
      Cmd_JoinLines <$> genLineNum b <*> genLineNum b

    execute (Cmd_JoinLines ln1 ln2) = evalIO $ do
      edCmdsOnFile edFile
        [ format (d%","%d%"j") ln1 ln2
        , "w"
        , "q"
        ]
      readEdFile edFile
  in
    Command gen execute
    [ Require $ \(Buffer b) (Cmd_JoinLines ln1 ln2) ->
        ln1 >= 0 && ln1 < ln2 && ln2 < getTextLength b && not (null b)
    , Update $ \(Buffer b) (Cmd_JoinLines ln1 ln2) _ ->
        Buffer
        . bifold
        . second (
            \content ->
              let
                parts = splitAt ((fromIntegral ln2) - (fromIntegral ln1) + 1) content
                joinedPart = (T.concat . fst) parts
                untouchedPart = snd parts
              in
                joinedPart : untouchedPart
        )
        $ splitAt ((fromIntegral ln1) - 1) b
    , Ensure $ \(Buffer old) (Buffer new) (Cmd_JoinLines ln1 ln2) out -> do
        T.unlines new === out
        length new === (length old) -  ((fromIntegral ln2) - (fromIntegral ln1) + 1) + 1
    ]


prop_ed_blackbox_file :: Property
prop_ed_blackbox_file = property $ do
  -- Create our file to apply our ed commands to
  edFile <- evalIO $ decodeString . fst <$> mkstemp "/tmp/ed_test_file_"

  let
    -- Prepare our list of possible commands
    cmds = ($ edFile) <$> [cAppendText, cPrintAll, cDeleteLine, cAppendAt, cJoinLines]
    -- Initialise our 'state'
    initialState = Buffer mempty

  -- Generate a sequence of Commands to apply to our state machine
  actions <- forAll $ Gen.sequential (Range.linear 1 100) initialState cmds

  -- Reset the ed buffer
  evalIO $ resetEdFile edFile

  -- Run the tests!
  executeSequential initialState actions

  -- Clean up our temp file
  -- This could be configurable so that on a failing test, we don't delete the file ?
  evalIO . sh $ rm edFile
