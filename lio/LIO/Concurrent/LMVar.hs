{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ConstraintKinds,
             FlexibleContexts #-}
{- |

This module implements labeled 'MVar's.  The interface is analogous to
"Control.Concurrent.MVar", but the operations take place in the 'LIO'
monad.  A labeled MVar, of type @'LMVar' l a@, is a mutable location
that can be in one of two states; an 'LMVar' can be empty, or it can
be full (with a value of type @a@). The location is protected by a
label of type 'l'.  As in the case of @LIORef@s (see "LIO.LIORef"),
this label is fixed and does not change according to the content
placed into the location.  Unlike @LIORef@s, most operations use
'guardWrite' or 'guardWriteP', reflecting the fact that there is no
such thing as read-only or write-only operations on an 'LMVar'.

'LMVar's can be used to build synchronization primitives and
communication channels ('LMVar's themselves are single-place
channels).  We refer to "Control.Concurrent.MVar" for the full
documentation on MVars.

-}

module LIO.Concurrent.LMVar (
    LMVar
  -- * Creating labeled 'MVar's
  , newEmptyLMVar, newEmptyLMVarP
  , newLMVar, newLMVarP
  -- * Take 'LMVar'
  , takeLMVar, takeLMVarP
  , tryTakeLMVar, tryTakeLMVarP
  -- * Put 'LMVar'
  , putLMVar, putLMVarP
  -- * Read 'LMVar'
  , tryPutLMVar, tryPutLMVarP
  , readLMVar, readLMVarP
  -- * Swap 'LMVar'
  , swapLMVar, swapLMVarP
  -- * Check state of 'LMVar'
  , isEmptyLMVar, isEmptyLMVarP
  ) where

import safe Control.Concurrent.MVar

import safe LIO.Core
import safe LIO.Error
import LIO.TCB
import LIO.TCB.LObj

import LIO.DCLabel

--
-- Creating labeled 'MVar's
--

-- | An @LMVar@ is a labeled synchronization variable (an 'MVar') that
-- can be used by concurrent threads to communicate.
type LMVar l a = LObj l (MVar a)

-- | Create a new labeled MVar, in an empty state. Note that the supplied
-- label must be above the current label and below the current clearance.
-- An exception will be thrown by the underlying 'guardAlloc' if this is
-- not the case.
newEmptyLMVar :: DCLabel                -- ^ Label of @LMVar@
              -> LIO DCLabel (LMVar DCLabel a)    -- ^ New mutable DCLabelocation
newEmptyLMVar l = do
  withContext "newEmptyLMVar" $ guardAlloc l
  ioTCB (LObjTCB l `fmap` newEmptyMVar)

-- | Same as 'newEmptyLMVar' except it takes a set of privileges which
-- are accounted for in comparing the label of the MVar to the current
-- label and clearance.
newEmptyLMVarP :: DCPriv -> DCLabel -> LIO DCLabel (LMVar DCLabel a)
newEmptyLMVarP p l = do
  withContext "newEmptyLMVarP" $ guardAllocP p l
  ioTCB $ LObjTCB l `fmap` newEmptyMVar

-- | Create a new labeled MVar, in an filled state with the supplied
-- value. Note that the supplied label must be above the current label
-- and below the current clearance.
newLMVar :: DCLabel                       -- ^ Label of @LMVar@
         -> a                       -- ^ Initial value of @LMVar@
         -> LIO DCLabel (LMVar DCLabel a)       -- ^ New mutable DCLabelocation
newLMVar l a = do
  withContext "newLMVar" $ guardAlloc l
  ioTCB (LObjTCB l `fmap` newMVar a)

-- | Same as 'newLMVar' except it takes a set of privileges which are
-- accounted for in comparing the label of the MVar to the current label
-- and clearance.
newLMVarP :: DCPriv -> DCLabel -> a -> LIO DCLabel (LMVar DCLabel a)
newLMVarP p l a = do
  withContext "newLMVarP" $ guardAllocP p l
  ioTCB $ LObjTCB l `fmap` newMVar a

--
-- Take 'LMVar'
--

-- | Return contents of the 'LMVar'. Note that a take consists of a read
-- and a write, since it observes whether or not the 'LMVar' is full, and
-- thus the current label must be the same as that of the 'LMVar' (of
-- course, this is not the case when using privileges).  Hence, if the
-- label of the 'LMVar' is below the current clearance, we raise the
-- current label to the join of the current label and the label of the
-- MVar and read the contents of the @MVar@. The underlying guard
-- 'guardWrite' will throw an exception if any of the IFC checks fail.
-- Finally, like 'MVars' if the 'LMVar' is empty, @takeLMVar@
-- blocks.
takeLMVar :: LMVar DCLabel a -> LIO DCLabel a
takeLMVar = blessTCB "takeLMVar" takeMVar

-- | Same as 'takeLMVar' except @takeLMVarP@ takes a privilege object
-- which is used when the current label is raised.
takeLMVarP :: DCPriv -> LMVar DCLabel a -> LIO DCLabel a
takeLMVarP = blessPTCB "takeLMVarP" takeMVar

-- | Non-blocking version of 'takeLMVar'. It returns @Nothing@ if the
-- 'LMVar' is empty, otherwise it returns @Just@ value, emptying the
-- 'LMVar'.
tryTakeLMVar :: LMVar DCLabel a -> LIO DCLabel (Maybe a)
tryTakeLMVar = blessTCB "tryTakeLMVar" tryTakeMVar

-- | Same as 'tryTakeLMVar', but uses priviliges when raising current
-- label.
tryTakeLMVarP :: DCPriv -> LMVar DCLabel a -> LIO DCLabel (Maybe a)
tryTakeLMVarP = blessPTCB "tryTakeLMVar" tryTakeMVar

--
-- Put 'LMVar'
--

-- | Puts a value into an 'LMVar'. Note that a put consists of a read and
-- a write, since it observes whether or not the 'LMVar' is empty, and so
-- the current label must be the same as that of the 'LMVar' (of course,
-- this is not the case when using privileges). As in the 'takeLMVar'
-- case, if the label of the 'LMVar' is below the current clearance, we
-- raise the current label to the join of the current label and the label
-- of the MVar and put the value into the @MVar@.  Moreover if these IFC
-- restrictions fail, the underlying 'guardWrite' throws an exception.
-- If the 'LMVar' is full, @putLMVar@ blocks.
putLMVar :: LMVar DCLabel a   -- ^ Source 'LMVar'
         -> a           -- ^ New value
         -> LIO DCLabel ()
putLMVar = blessTCB "putLMVar" putMVar

-- | Same as 'putLMVar' except @putLMVarP@ takes a privilege object
-- which is used when the current label is raised.
putLMVarP :: DCPriv -> LMVar DCLabel a -> a -> LIO DCLabel ()
putLMVarP = blessPTCB "putLMVarP" putMVar

-- | Non-blocking version of 'putLMVar'. It returns @True@ if the
-- 'LMVar' was empty and the put succeeded, otherwise it returns @False@.
tryPutLMVar :: LMVar DCLabel a -> a -> LIO DCLabel Bool
tryPutLMVar = blessTCB "tryPutLMVar" tryPutMVar

-- | Same as 'tryPutLMVar', but uses privileges when raising current label.
tryPutLMVarP :: DCPriv -> LMVar DCLabel a -> a -> LIO DCLabel Bool
tryPutLMVarP = blessPTCB "tryPutLMVarP" tryPutMVar

--
-- Read 'LMVar'
--

-- | Combination of 'takeLMVar' and 'putLMVar'. Read the value, and
-- just put it back. This operation is not atomic, and can can result
-- in unexpected outcomes if another thread is simultaneously calling
-- a function such as 'putLMVar', 'tryTakeLMVarP', or 'isEmptyLMVar'
-- for this 'LMVar'.
readLMVar :: LMVar DCLabel a -> LIO DCLabel a
readLMVar = blessTCB "readLMVar" readMVar

-- | Same as 'readLMVar' except @readLMVarP@ takes a privilege object
-- which is used when the current label is raised.
readLMVarP :: DCPriv -> LMVar DCLabel a -> LIO DCLabel a
readLMVarP = blessPTCB "readLMVarP" readMVar

--
-- Swap 'LMVar'
--

-- | Takes a value from an 'LMVar', puts a new value into the 'LMvar',
-- and returns the taken value.  Like the other 'LMVar' operations it is
-- required that the label of the 'LMVar' be above the current label and
-- below the current clearance. Moreover, the current label is raised to
-- accommodate for the observation. The underlying 'guardWrite' throws an
-- exception if this cannot be accomplished. This operation is atomic iff
-- there is no other thread calling 'putLMVar' for this 'LMVar'.
swapLMVar :: LMVar DCLabel a          -- ^ Source @LMVar@
          -> a                  -- ^ New value
          -> LIO DCLabel a            -- ^ Taken value
swapLMVar = blessTCB "swapLMVar" swapMVar

-- | Same as 'swapLMVar' except @swapLMVarP@ takes a privilege object
-- which is used when the current label is raised.
swapLMVarP :: DCPriv -> LMVar DCLabel a -> a -> LIO DCLabel a
swapLMVarP = blessPTCB "swapLMVarP" swapMVar

--
-- Check state of 'LMVar'
--

-- | Check the status of an 'LMVar', i.e., whether it is empty. The
-- function succeeds if the label of the 'LMVar' is below the current
-- clearance -- the current label is raised to the join of the 'LMVar'
-- label and the current label.
isEmptyLMVar :: LMVar DCLabel a -> LIO DCLabel Bool
isEmptyLMVar = blessTCB "isEmptyLMVar" isEmptyMVar

-- | Same as 'isEmptyLMVar', but uses privileges when raising current label.
isEmptyLMVarP :: DCPriv -> LMVar DCLabel a -> LIO DCLabel Bool
isEmptyLMVarP = blessPTCB "isEmptyLMVarP" isEmptyMVar
