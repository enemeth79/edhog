{-# LANGUAGE OverloadedStrings #-}
module Ed.Memory where

import           Control.Applicative    (liftA2)
import           Control.Lens           (ix, snoc, (%~), (.~),
                                         (^.), (^?))
import           Control.Monad.IO.Class (MonadIO)

import           System.Timeout         (timeout)

import           Data.Bifoldable        (bifold)
import           Data.Bifunctor         (first, second)
import           Data.Foldable          (traverse_)
import           Data.Function          ((&))

import           Text.Read              (readMaybe)

import           Data.Text              (Text)
import qualified Data.Text              as T
import qualified Data.Text.IO           as T

import           Hedgehog

import qualified Hedgehog.Gen           as Gen
import qualified Hedgehog.Range         as Range

import Ed.Types

genSafeLineNum :: (HasEdModel s v, MonadGen m) => s -> m Word
genSafeLineNum = Gen.word . Range.linear 1 . bufferLength

genTextInp :: MonadGen m => m Text
genTextInp = Gen.text (Range.linear 1 100) Gen.alphaNum

cAppendText
  :: ( MonadGen g
     , MonadIO m
     , MonadTest m
     )
  => EdProc
  -> Command g m EdModel
cAppendText edProc =
  let
    gen _ = Just $ Cmd_Append <$> genTextInp

    execute (Cmd_Append t) = evalIO $
      traverse_ (edCmd edProc)
        [ "a"
        , t
        , "."
        ]
      *> getBlackBoxState edProc
  in
    Command gen execute
    [ Update $ \ed (Cmd_Append i) _ -> ed
      & edBuffer %~ flip snoc i
      & edAddress .~ if emptyBuffer ed then 1 else bufferLength ed + 1

    , Ensure $ \edOld edNew (Cmd_Append i) bbEd -> do
        edNew ^? edAddress === bbEd ^. bbEdAddress
        edNew ^. edBuffer === snoc (edOld ^. edBuffer) i
        fromModelBuffer edNew === bbEd ^. bbEdBuffer
    ]

cDeleteLine
  :: ( MonadIO m
     , MonadTest m
     , MonadGen g
     )
  => EdProc
  -> Command g m EdModel
cDeleteLine edProc =
  let
    gen = Just . fmap Cmd_DeleteLine . genSafeLineNum

    execute (Cmd_DeleteLine n) = evalIO $ do
      edCmd edProc (singleAddrCmd 'd' n)
      getBlackBoxState edProc
  in
    Command gen execute
    [ Require $ \ed (Cmd_DeleteLine ln) ->
        addressInBuffer ed ln

    , Update $ \ed (Cmd_DeleteLine n) _ -> ed
        & edBuffer %~ bifold . first (take (fromIntegral n - 1)) . splitAt (fromIntegral n)
        & edAddress .~ n

    , Ensure $ \edOld edNew (Cmd_DeleteLine n) bbEd -> do
        let
          newB = edNew ^. edBuffer
          oldB = edOld ^. edBuffer

        fromModelBuffer edNew === bbEd ^. bbEdBuffer
        edNew ^? edAddress === bbEd ^. bbEdAddress

        let n' = fromIntegral n

        newB ^? ix n'       === oldB ^? ix (n' + 1)
        newB ^? ix (n' - 1) === oldB ^? ix n'
    ]


cAppendAt
  :: ( MonadGen g
     , MonadIO m
     , MonadTest m
     )
  => EdProc
  -> Command g m EdModel
cAppendAt edProc =
  let
    gen b = Just $ Cmd_AppendAt
      <$> genSafeLineNum b
      <*> genTextInp

    execute (Cmd_AppendAt ln i) = evalIO $
      traverse_ (edCmd edProc)
        [ singleAddrCmd 'a' ln
        , i
        , "."
        ]
      *> getBlackBoxState edProc
  in
    Command gen execute
    [ Require $ \ed (Cmd_AppendAt ln _) ->
        addressInBuffer ed ln

    , Update $ \ed (Cmd_AppendAt ln i) _ -> ed
      & edBuffer %~ bifold . second (i:) . splitAt (fromIntegral ln)
      -- We end on the line following the append
      & edAddress .~ ln + 1

    , Ensure $ \_ edNew (Cmd_AppendAt ln i) bbEd -> do
        fromModelBuffer edNew === bbEd ^. bbEdBuffer

        edNew ^? edAddress === bbEd ^. bbEdAddress
        edNew ^? edBuffer . ix (fromIntegral ln) === Just i
    ]


-- Joins the addressed lines, replacing them by a single line containing their joined text.
-- If only one address is given, this command does nothing.
-- If lines are joined, the current address is set to the address of the joined line.
-- Else, the current address is unchanged.
cJoinLines
  :: ( MonadGen g
     , MonadIO m
     , MonadTest m
     )
  => EdProc
  -> Command g m EdModel
cJoinLines edProc =
  let
    gen b = Just $ Cmd_JoinLines
      <$> genSafeLineNum b
      <*> genSafeLineNum b

    execute (Cmd_JoinLines ln1 ln2) = evalIO $ do
      edCmd edProc (rangeAddrCmd 'j' ln1 ln2)
      getBlackBoxState edProc
  in
    Command gen execute
    [ Require $ \ed (Cmd_JoinLines ln1 ln2) ->
        ln1 < ln2 && (addressInBuffer ed ln1) && (addressInBuffer ed ln2)

    , Update $ \ed (Cmd_JoinLines ln1 ln2) _ -> ed
        &  edBuffer %~
          bifold
          . second (
              \content ->
                let
                  parts = splitAt ((fromIntegral ln2) - (fromIntegral ln1) + 1) content
                  joinedPart = (T.concat . fst) parts
                  untouchedPart = snd parts
                in
                  joinedPart : untouchedPart
          )
          . splitAt ((fromIntegral ln1) - 1)
        & edAddress .~ ln1

    , Ensure $ \edOld edNew (Cmd_JoinLines ln1 ln2) bbEd -> do
       -- TODO
        -- fromModelBuffer edNew === bbEd ^. bbEdBuffer
        -- bufferLength edNew === (bufferLength edOld) - ((fromIntegral ln2) - (fromIntegral ln1) + 1) + 1
       -- TODO
        -- getTextLength new === (getTextLength old) - ((fromIntegral ln2) - (fromIntegral ln1) + 1) + 1

        edNew ^? edAddress === bbEd ^. bbEdAddress
    ]
edCmd :: EdProc -> Text -> IO ()
edCmd p c = T.hPutStrLn (_edIn p) c

readEdLine :: EdProc -> IO (Maybe Text)
readEdLine = timeout 2500 . T.hGetLine . _edOut

getCurrentLine :: EdProc -> IO (Maybe Word)
getCurrentLine ed = fmap (readMaybe . T.unpack =<<)
  $ edCmd ed ".=" *> readEdLine ed

readEntireBuffer :: EdProc -> IO Text
readEntireBuffer ed = edCmd ed ",p" *> go []
  where
    go acc = readEdLine ed
      >>= maybe (pure . T.unlines . reverse $ acc) (go . (:acc))

-- Must get address before reading the entire buffer as reading the buffer will
-- change the address.
getBlackBoxState :: EdProc -> IO BBEd
getBlackBoxState ed = liftA2 BBEd (getCurrentLine ed) (readEntireBuffer ed)

prop_ed_blackbox_memory :: EdProc -> Property
prop_ed_blackbox_memory edProc = property $ do
  let
    cmds = ($ edProc) <$>
      [ cAppendText
      , cAppendAt
      , cDeleteLine
      , cJoinLines
      ]

    initialState = EdModel mempty 0

  actions <- forAll $ Gen.sequential (Range.linear 1 20) initialState cmds

  -- Reset the ed buffer
  evalIO $ do
    edCmd edProc "a"
    edCmd edProc "avoiding invalid address error"
    edCmd edProc "."
    edCmd edProc ",d"

  executeSequential initialState actions
