{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}
module Ed.Types where

import           Control.Lens   (folded, lengthOf, makeClassy, nullOf, view, to)
import           Hedgehog       (HTraversable (..))

import           System.IO      (Handle)
import qualified System.Process as P

import           Data.Text      (Text, pack)
import qualified Data.Text as T

import           Text.Printf            (printf)

-- @/bin/ed@ Process
data EdProc = EdProc
  { _edIn  :: Handle
  , _edOut :: Handle
  , _edPh  :: P.ProcessHandle
  }

-- The model of ed
data EdModel (v :: * -> *) = EdModel
  { _edBuffer  :: [Text]
  , _edAddress :: Word
  }
  deriving (Eq, Show)
makeClassy ''EdModel

singleAddrCmd :: Char -> Word -> Text
singleAddrCmd cmd w = pack $ printf "%u%c" w cmd

rangeAddrCmd :: Char -> Word -> Word -> Text
rangeAddrCmd cmd s e = pack $ printf "%u,%u%c" cmd s e

bufferLength :: HasEdModel s v => s -> Word
bufferLength = fromIntegral . lengthOf (edBuffer . folded)

fromModelBuffer :: HasEdModel s v => s -> Text
fromModelBuffer = view (edBuffer . to T.unlines)

emptyBuffer :: HasEdModel s v => s -> Bool
emptyBuffer = nullOf (edBuffer . folded)

addressInBuffer :: HasEdModel s v => s -> Word -> Bool
addressInBuffer ed ln = ln < bufferLength ed && not (emptyBuffer ed)

-- The black box of @/bin/ed@
data BBEd = BBEd
  { _bbEdAddress :: Maybe Word
  , _bbEdBuffer  :: Text
  }
  deriving (Eq, Show)
makeClassy ''BBEd

-- Commands!
data Cmd_AppendAt (v :: * -> *) =
  Cmd_AppendAt Word Text
  deriving (Show, Eq)

instance HTraversable Cmd_AppendAt where
  htraverse _ (Cmd_AppendAt n t) = pure (Cmd_AppendAt n t)

data Cmd_PrintAll (v :: * -> *) =
  Cmd_PrintAll
  deriving (Show, Eq)

instance HTraversable Cmd_PrintAll where
  htraverse _ _ = pure Cmd_PrintAll

newtype Cmd_Append (v :: * -> *) =
  Cmd_Append Text
  deriving (Show, Eq)

instance HTraversable Cmd_Append where
  htraverse _ (Cmd_Append t) = pure (Cmd_Append t)

newtype Cmd_DeleteLine (v :: * -> *) =
  Cmd_DeleteLine Word
  deriving (Show, Eq)

instance HTraversable Cmd_DeleteLine where
  htraverse _ (Cmd_DeleteLine t) = pure (Cmd_DeleteLine t)

data Cmd_JoinLines (v :: * -> *) =
  Cmd_JoinLines Word Word
  deriving (Show, Eq)

instance HTraversable Cmd_JoinLines where
  htraverse _ (Cmd_JoinLines n1 n2) = pure (Cmd_JoinLines n1 n2)
