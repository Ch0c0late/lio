{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ConstraintKinds,
             FlexibleContexts #-}

{- |

Mutable reference in the 'LIO' monad. As with other objects in LIO,
mutable references have an associated label that is used to impose
restrictions on its operations. In fact, labeled references
('LIORef's) are simply labeled 'IORef's with read and write access
restricted according to the label. This module is analogous to
"Data.IORef", but the operations take place in the 'LIO' monad.

-}


module LIO.LIORef (
    LIORef
  -- * Basic Functions
  -- ** Create labeled 'IORef's
  , newLIORef, newLIORefP
  -- ** Read 'LIORef's
  , readLIORef, readLIORefP
  -- ** Write 'LIORef's
  , writeLIORef, writeLIORefP
  -- ** Modify 'LIORef's
  , modifyLIORef
  ) where

import safe Data.IORef

import safe LIO.Core
import safe LIO.Error
import LIO.TCB
import LIO.TCB.LObj
import LIO.DCLabel

import LIO.RCLabel
import LIO.SafeCopy

--
-- Create labeled 'IORef's
--

-- | An @LIORef@ is an @IORef@ with an associated, fixed label.  The
-- restriction to an immutable label comes from the fact that it is
-- possible to leak information through the label itself, since we
-- wish to allow @LIORef@ to be an instance of 'LabelOf'.  Of course,
-- you can create an @LIORef@ of 'Labeled' to get a limited form of
-- flow-sensitivity.
type LIORef l a = LObj l (IORef (MultiRCRef a))

-- | Create a new reference with a particularlabel.  The label
-- specified must be between the thread's current label and clearance,
-- as enforced by 'guardAlloc'.
newLIORef :: DCLabel             -- ^ Label of reference
          -> a                  -- ^ Initial value
          -> LIO DCLabel (LIORef DCLabel a) -- ^ Mutable reference
newLIORef l a = do
  withContext "newLIORef" $ guardAlloc l
  fmap (LObjTCB l) (ioTCB . newIORef =<< multiAlloc l a)

-- | Same as 'newLIORef' except @newLIORefP@ takes privileges which
-- make the comparison to the current label more permissive, as
-- enforced by 'guardAllocP'.
newLIORefP :: DCPriv -> DCLabel -> Transfer a -> a -> LIO DCLabel (LIORef DCLabel a)
newLIORefP p l t a = do
  withContext "newLIORefP" $ guardAllocP p l
  fmap (LObjTCB l) (ioTCB . newIORef =<< multiAllocP p l t a)

--
-- Read 'LIORef's
--

-- | Read the value of a labeled reference. A read succeeds only if
-- the label of the reference is below the current
-- clearance. Moreover, the current label is raised to the 'lub' of
-- the current label and the reference label.  To avoid failures
-- (introduced by the 'taint' guard) use 'labelOf' to check that a
-- read will succeed.
readLIORef :: LIORef DCLabel a -> LIO DCLabel a
readLIORef (LObjTCB l r) = do
  old_state <- getLIOStateTCB
  withContext "readLIORef" $ taint l
  multiTaint old_state l =<< ioTCB (readIORef r)

-- | Same as 'readLIORef', except @readLIORefP@ takes a privilege
-- object which is used when the current label is raised (using
-- 'taintP' instead of 'taint').
readLIORefP :: DCPriv -> Transfer a -> LIORef DCLabel a -> LIO DCLabel a
readLIORefP p t (LObjTCB l r) = do
  old_state <- getLIOStateTCB
  withContext "readLIORefP" $ taintP p l
  multiTaintP old_state p l t =<< ioTCB (readIORef r)

--
-- Write 'LIORef's
--

-- | Write a new value into a labeled reference. A write succeeds if
-- the current label can-flow-to the label of the reference, and the
-- label of the reference can-flow-to the current clearance. Otherwise,
-- an exception is raised by the underlying 'guardAlloc' guard.
writeLIORef :: LIORef DCLabel a -> a -> LIO DCLabel ()
writeLIORef (LObjTCB l r) a = do
  withContext "writeLIORef" $ guardAlloc l
  ioTCB . writeIORef r =<< multiAlloc l a

-- | Same as 'writeLIORef' except @writeLIORefP@ takes a set of
-- privileges which are accounted for in comparing the label of the
-- reference to the current label.
writeLIORefP :: DCPriv -> LIORef DCLabel a -> Transfer a -> a -> LIO DCLabel ()
writeLIORefP p (LObjTCB l r) t a = do
  withContext "writeLIORefP" $ guardAllocP p l
  ioTCB . writeIORef r =<< multiAllocP p l t a

--
-- Modify 'LIORef's
--

-- | Mutate the contents of a labeled reference.  The mutation is
-- performed by a a pure function, which, because of laziness, is not
-- actually evaluated until such point as a (possibly higher-labeled)
-- thread actually reads the 'LIORef'.  The caller of @modifyLIORef@
-- learns no information about the previous contents the 'LIORef'.
-- For that reason, there is no need to raise the current label.  The
-- `LIORef`'s label must still lie between the current label and
-- clearance, however (as enforced by 'guardAlloc').
modifyLIORef :: LIORef DCLabel a            -- ^ Labeled reference
             -> (a -> a)               -- ^ Modifier
             -> LIO DCLabel ()
modifyLIORef (LObjTCB l r) f = do
  withContext "modifyLIORef" $ guardAlloc l
  x <- ioTCB $ readIORef r
  x' <- ioTCB $ multiFmap l f x
  ioTCB $ writeIORef r x'

-- NB: The following function requires us to have a transfer function for
-- *functions*.  For now this is disallowed.

-- | Like 'modifyLIORef', but takes a privilege argument and guards
-- execution with 'guardAllocP' instead of 'guardAlloc'.
-- modifyLIORefP :: DCPriv -> LIORef DCLabel a -> (a -> a) -> LIO DCLabel ()
-- modifyLIORefP p (LObjTCB l r) f = do

-- NB: We can't implement either of these for full MultiRCRefs; it
-- should be possible to do them for AllRCRefs, however.  For now skip.

-- | Atomically modifies the contents of an 'LIORef'. It is required
-- that the label of the reference be above the current label, but
-- below the current clearance. Moreover, since this function can be
-- used to directly read the value of the stored reference, the
-- computation is \"tainted\" by the reference label (i.e., the
-- current label is raised to the 'join' of the current and reference
-- labels). These checks and label raise are done by 'guardWrite',
-- which will raise a 'LabelError' exception if any of the IFC
-- conditions cannot be satisfied.
-- atomicModifyLIORef :: LIORef DCLabel a -> (a -> (a, b)) -> LIO DCLabel b
-- atomicModifyLIORef = blessTCB "atomicModifyIORef" atomicModifyIORef

-- | Same as 'atomicModifyLIORef' except @atomicModifyLIORefP@ takes a
-- set of privileges and uses 'guardWriteP' instead of 'guardWrite'.
--  atomicModifyLIORefP :: Priv CNF -> LIORef DCLabel a -> (a -> (a, b)) -> LIO DCLabel b
--  atomicModifyLIORefP = blessPTCB "atomicModifyIORef" atomicModifyIORef

