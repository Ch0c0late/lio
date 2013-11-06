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
import safe Data.Traversable

import safe LIO.Core
import safe LIO.Error
import LIO.TCB
import LIO.TCB.LObj

import LIO.RCLabel
import LIO.SafeCopy

import LIO.DCLabel

--
-- Creating labeled 'MVar's
--

-- | An @LMVar@ is a labeled synchronization variable (an 'MVar') that
-- can be used by concurrent threads to communicate.
type LMVar l a = LObj l (MVar (MultiRCRef a))

-- | Create a new labeled MVar, in an empty state. Note that the supplied
-- label must be above the current label and below the current clearance.
-- An exception will be thrown by the underlying 'guardAlloc' if this is
-- not the case.
newEmptyLMVar :: DCLabel                -- ^ Label of @LMVar@
              -> LIO DCLabel (LMVar DCLabel a)    -- ^ New mutable DCLabelocation
newEmptyLMVar l = do
  withContext "newEmptyLMVar" $ guardAlloc l
  LObjTCB l `fmap` ioTCB newEmptyMVar

-- | Same as 'newEmptyLMVar' except it takes a set of privileges which
-- are accounted for in comparing the label of the MVar to the current
-- label and clearance.
newEmptyLMVarP :: DCPriv -> DCLabel -> LIO DCLabel (LMVar DCLabel a)
newEmptyLMVarP p l = do
  withContext "newEmptyLMVarP" $ guardAllocP p l
  LObjTCB l `fmap` ioTCB newEmptyMVar

-- | Create a new labeled MVar, in an filled state with the supplied
-- value. Note that the supplied label must be above the current label
-- and below the current clearance.
newLMVar :: DCLabel                       -- ^ Label of @LMVar@
         -> a                       -- ^ Initial value of @LMVar@
         -> LIO DCLabel (LMVar DCLabel a)       -- ^ New mutable DCLabelocation
newLMVar l a = do
  withContext "newLMVar" $ guardAlloc l
  fmap (LObjTCB l) (ioTCB . newMVar =<< multiAlloc l a)

-- | Same as 'newLMVar' except it takes a set of privileges which are
-- accounted for in comparing the label of the MVar to the current label
-- and clearance.
newLMVarP :: DCPriv -> DCLabel -> Transfer a -> a -> LIO DCLabel (LMVar DCLabel a)
newLMVarP p l t a = do
  withContext "newLMVarP" $ guardAllocP p l
  fmap (LObjTCB l) (ioTCB . newMVar =<< multiAllocP p l t a)

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
--
-- [RC] Note that for resource containers, we don't care about blocking
-- behavior.
takeLMVar :: LMVar DCLabel a -> LIO DCLabel a
takeLMVar (LObjTCB l r) = do
    old_state <- getLIOStateTCB
    withContext "takeLMVar" $ guardWrite l
    multiTaint old_state l =<< ioTCB (takeMVar r)

-- | Same as 'takeLMVar' except @takeLMVarP@ takes a privilege object
-- which is used when the current label is raised.
takeLMVarP :: DCPriv -> Transfer a -> LMVar DCLabel a -> LIO DCLabel a
takeLMVarP p t (LObjTCB l r) = do
    old_state <- getLIOStateTCB
    withContext "takeLMVarP" $ guardWriteP p l
    multiTaintP old_state p l t =<< ioTCB (takeMVar r)

-- | Non-blocking version of 'takeLMVar'. It returns @Nothing@ if the
-- 'LMVar' is empty, otherwise it returns @Just@ value, emptying the
-- 'LMVar'.
tryTakeLMVar :: LMVar DCLabel a -> LIO DCLabel (Maybe a)
tryTakeLMVar (LObjTCB l r) = do
    old_state <- getLIOStateTCB
    withContext "tryTakeLMVar" $ guardWrite l
    traverse (multiTaint old_state l) =<< ioTCB (tryTakeMVar r)

-- | Same as 'tryTakeLMVar', but uses priviliges when raising current
-- label.
tryTakeLMVarP :: DCPriv -> Transfer a -> LMVar DCLabel a -> LIO DCLabel (Maybe a)
tryTakeLMVarP p t (LObjTCB l r) = do
    old_state <- getLIOStateTCB
    withContext "tryTakeLMVarP" $ guardWriteP p l
    traverse (multiTaintP old_state p l t) =<< ioTCB (tryTakeMVar r)

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
putLMVar (LObjTCB l r) a = do
    withContext "putLMVar" $ guardWrite l
    ioTCB . putMVar r =<< multiAlloc l a

-- | Same as 'putLMVar' except @putLMVarP@ takes a privilege object
-- which is used when the current label is raised.
putLMVarP :: DCPriv -> LMVar DCLabel a -> Transfer a -> a -> LIO DCLabel ()
putLMVarP p (LObjTCB l r) t a = do
  withContext "putLMVarP" $ guardWriteP p l
  ioTCB . putMVar r =<< multiAllocP p l t a

-- | Non-blocking version of 'putLMVar'. It returns @True@ if the
-- 'LMVar' was empty and the put succeeded, otherwise it returns @False@.
tryPutLMVar :: LMVar DCLabel a -> a -> LIO DCLabel Bool
tryPutLMVar (LObjTCB l r) a = do
    withContext "tryPutLMVar" $ guardWrite l
    ioTCB . tryPutMVar r =<< multiAlloc l a

-- | Same as 'tryPutLMVar', but uses privileges when raising current label.
tryPutLMVarP :: DCPriv -> LMVar DCLabel a -> Transfer a -> a -> LIO DCLabel Bool
tryPutLMVarP p (LObjTCB l r) t a = do
  withContext "tryPutLMVarP" $ guardWriteP p l
  ioTCB . tryPutMVar r =<< multiAllocP p l t a

--
-- Read 'LMVar'
--

-- | Combination of 'takeLMVar' and 'putLMVar'. Read the value, and
-- just put it back. This operation is not atomic, and can can result
-- in unexpected outcomes if another thread is simultaneously calling
-- a function such as 'putLMVar', 'tryTakeLMVarP', or 'isEmptyLMVar'
-- for this 'LMVar'.
readLMVar :: LMVar DCLabel a -> LIO DCLabel a
readLMVar (LObjTCB l r) = do
    old_state <- getLIOStateTCB
    withContext "readLMVar" $ guardWrite l
    multiTaint old_state l =<< ioTCB (readMVar r)

-- | Same as 'readLMVar' except @readLMVarP@ takes a privilege object
-- which is used when the current label is raised.
readLMVarP :: DCPriv -> Transfer a -> LMVar DCLabel a -> LIO DCLabel a
readLMVarP p t (LObjTCB l r) = do
    old_state <- getLIOStateTCB
    withContext "readLMVarP" $ guardWriteP p l
    multiTaintP old_state p l t =<< ioTCB (readMVar r)

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
swapLMVar (LObjTCB l r) a = do
    old_state <- getLIOStateTCB
    withContext "swapLMVar" $ guardWrite l
    a' <- multiAlloc l a
    multiTaint old_state l =<< ioTCB (swapMVar r a')

-- | Same as 'swapLMVar' except @swapLMVarP@ takes a privilege object
-- which is used when the current label is raised.
swapLMVarP :: DCPriv -> Transfer a -> LMVar DCLabel a -> Transfer a -> a -> LIO DCLabel a
swapLMVarP p t1 (LObjTCB l r) t2 a = do
    old_state <- getLIOStateTCB
    withContext "swapLMVarP" $ guardWriteP p l
    a' <- multiAllocP p l t2 a
    multiTaintP old_state p l t1 =<< ioTCB (swapMVar r a')

--
-- Check state of 'LMVar'
--

-- ToDo: it seems this shouldn't apply the write condition

-- | Check the status of an 'LMVar', i.e., whether it is empty. The
-- function succeeds if the label of the 'LMVar' is below the current
-- clearance -- the current label is raised to the join of the 'LMVar'
-- label and the current label.
isEmptyLMVar :: LMVar DCLabel a -> LIO DCLabel Bool
isEmptyLMVar (LObjTCB l r) = do
    withContext "isEmptyLMVar" $ guardWrite l
    ioTCB (isEmptyMVar r)

-- | Same as 'isEmptyLMVar', but uses privileges when raising current label.
isEmptyLMVarP :: DCPriv -> LMVar DCLabel a -> LIO DCLabel Bool
isEmptyLMVarP p (LObjTCB l r) = do
    withContext "isEmptyLMVarP" $ guardWriteP p l
    ioTCB (isEmptyMVar r)
