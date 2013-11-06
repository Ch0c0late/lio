{-# LANGUAGE Unsafe #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE CPP #-}

-- | This module provides routines for safely exposing IO functions in
-- the 'LIO' monad.  At a high level, certain IO objects such as
-- handles can be associated with a label via 'LObj', while certain
-- operations can then be blessed (via 'blessTCB') to operate on such
-- 'LObj' objects.
--
-- For example, trusted code might define the following:
--
-- > import qualified System.IO as IO
-- > 
-- > type Handle = LObj DCLabel IO.Handle
-- > 
-- > hPutStrLn :: LObj DCLabel IO.Handle -> String -> LIO DCLabel ()
-- > hPutStrLn h = blessTCB "hPutStrLn" IO.hPutStrLn h
-- >
-- > hPutStrLnP :: DCPriv -> LObj DCLabel IO.Handle -> String -> LIO DCLabel ()
-- > hPutStrLnP h = blessPTCB "hPutStrLnP" IO.hPutStrLn h
-- > 
-- > hGetLine :: LObj DCLabel IO.Handle -> LIO DCLabel String
-- > hGetLine h = blessTCB "hGetLine" IO.hGetLine h
--
-- Then application-specific trusted code can wrap a specific label
-- around each 'Handle' using the 'LObjTCB' constructor.
module LIO.TCB.LObj (LObj(..)) where

import safe Data.Typeable

import safe LIO.Core
import safe LIO.Error
import safe LIO.Label
import LIO.TCB

-- | A \"@LObj label object@\" is a wrapper around an IO abstraction
-- of type @object@ (such as a file handle or socket) on which it is
-- safe to do @IO@ operations in the 'LIO' monad when the caller can
-- read and write a the label @label@.  It is the job of the trusted
-- code constructing such a @LObj@ object to ensure both that the same
-- IO object is only ever associated with a single label, and that the
-- abstraction combined with its blessed IO operations (see
-- 'blessTCB') cannot be used to communicate with code running at
-- different labels.
data LObj label object = LObjTCB !label !object deriving (Typeable)

instance LabelOf LObj where
  {-# INLINE labelOf #-}
  labelOf (LObjTCB l _) = l

