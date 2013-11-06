{-# LANGUAGE Trustworthy #-}

{- |

A data type 'Labeled' protects access to pure values (hence, we refer
to values of type @'Label' a@ as /labeled values/).  The role of
labeled values is to allow users to associate heterogeneous labels (see
"LIO.Label") with values. Although LIO\'s current label protects all
values in scope with the current label, 'Labeled' values allow for
more fine grained protection. Moreover, trusted code may easily
inspect 'Labeled' values, for instance, when inserting values into a
database.

Without the appropriate privileges, one cannot produce a pure
/unlabeled/ value that depends on a secret 'Labeled' value, or
conversely produce a high-integrity 'Labeled' value based on pure
data.  This module exports functions for creating labeled values
('label'), using the values protected by 'Labeled' by unlabeling them
('unlabel'), and changing the value of a labeled value without
inspection ('relabelLabeledP', 'taintLabeled').  

Two 'Applicative' 'Functor'-like operations are also defined for
'Labeled' data, namely 'lFmap' and 'lAp'.

-}

-- XXX WITH ASYNCHRONOUS CLEARANCE CHANGE THESE SHOULD BE FAILABLE!!!

module LIO.Labeled (
    Labeled, LabelOf(..)
  , DCLabeled
  -- * Label values
  , label, labelP
  -- * Unlabel values
  , unlabel, unlabelP
  -- * Relabel values
  , relabelLabeledP
  , taintLabeled, taintLabeledP 
  , lFmap
  ) where

import safe Control.Monad

import safe LIO.Error
import safe LIO.Label
import safe LIO.Core
import LIO.TCB
import LIO.SafeCopy

import LIO.DCLabel
import LIO.RCLabel

-- | An alias for 'Labeled' values labeled with a 'DCLabel'.
type DCLabeled = Labeled DCLabel

--
-- Label values
--

-- | Function to construct a 'Labeled' value from a label and a pure
-- value.  If the current label is @lcurrent@ and the current
-- clearance is @ccurrent@, then the label @l@ specified must satisfy
-- @lcurrent ``canFlowTo`` l && l ``canFlowTo`` ccurrent@. Otherwise
-- an exception is thrown (see 'guardAlloc').
label :: DCLabel -> a -> LIO DCLabel (Labeled DCLabel a)
label l a = do
    withContext "label" $ guardAlloc l
    LabeledTCB l `fmap` multiAlloc l a

-- | Constructs a 'Labeled' value using privilege to allow the value's
-- label to be below the current label.  If the current label is
-- @lcurrent@ and the current clearance is @ccurrent@, then the
-- privilege @p@ and label @l@ specified must satisfy @canFlowTo p
-- lcurrent l@ and @l ``canFlowTo`` ccurrent@.  Note that privilege is
-- not used to bypass the clearance.  You must use 'setClearanceP' to
-- raise the clearance first if you wish to create a 'Labeled' value
-- at a higher label than the current clearance.
labelP :: DCPriv -> DCLabel -> Transfer a -> a -> LIO DCLabel (Labeled DCLabel a)
labelP p newl t a = do
    withContext "labelP" $ guardAllocP p newl
    LabeledTCB newl `fmap` multiAllocP p newl t a

--
-- Unlabel values
--

-- | Within the 'LIO' monad, this function takes a 'Labeled' value and
-- returns it as an unprotected value of the inner type.  For
-- instance, in the 'LIO' monad one can say:
--
-- > x <- unlabel (lx :: Labeled SomeLabelType Int)
--
-- And now it is possible to use the pure value @x :: Int@, which was
-- previously protected by a label in @lx@.
--
-- @unlabel@ raises the current label as needed to reflect the fact
-- that the thread's behavior can now depend on the contents of @lx@.
-- If @unlabel@ing a value would require raising the current label
-- above the current clearance, then @unlabel@ throws an exception of
-- type 'LabelError'.  You can use 'labelOf' to check beforehand
-- whether 'unlabel' will succeed.
unlabel :: Labeled DCLabel a -> LIO DCLabel a
unlabel (LabeledTCB l v) = do
    old_state <- getLIOStateTCB
    withContext "unlabel" (taint l)
    multiTaint old_state l v

-- | Extracts the contents of a 'Labeled' value just like 'unlabel',
-- but takes a privilege argument to minimize the amount the current
-- label must be raised.  The privilege is used to raise the current
-- label less than might be required otherwise, but this function does
-- not change the current clarance and still throws a 'LabelError' if
-- the privileges supplied are insufficient to save the current label
-- from needing to exceed the current clearance.
-- 
-- [RC] In the container interpretation, this doesn't really work for
-- integrity because it is akin to saying, "Hey, I know you're already
-- dead, but don't worry, I'm willing to copy the data (endorse it)."
-- So we just go ahead and try to read the data, and then copy it to our
-- stuff
unlabelP :: DCPriv -> Transfer a -> Labeled DCLabel a -> LIO DCLabel a
unlabelP p t (LabeledTCB l v) = do
    old_state <- getLIOStateTCB
    withContext "unlabelP" (taintP p l)
    multiTaintP old_state p l t v

--
-- Relabel values
--

-- | Relabels a 'Labeled' value to the supplied label if the given
-- privileges permit it.  An exception is thrown unless the following
-- two conditions hold:
--
--   1. The new label must be below the current clearance.
--
--   2. The old label and new label must be equal (modulo privileges),
--   as enforced by 'canFlowToP'.
--
relabelLabeledP :: DCPriv -> DCLabel -> Transfer a -> Labeled DCLabel a -> LIO DCLabel (Labeled DCLabel a)
relabelLabeledP p newl t (LabeledTCB oldl v) = do
  clr <- getClearance
  unless (canFlowTo newl clr     &&
          canFlowToP p newl oldl &&
          canFlowToP p oldl newl) $ labelErrorP "relabelLabeledP" p [oldl, newl]
  state <- getLIOStateTCB
  r <- forM (cToList (dcIntegrity newl)) $ \goal -> do
    -- we're not storing the value, so label raise not necessary
    (_, r) <- multiExtractP state p (cSingleton goal) t v
    ioTCB $ wrapRCRef goal r
  return $ LabeledTCB newl r

-- | Raises the label of a 'Labeled' value to the 'lub' of it's
-- current label and the value supplied.  The label supplied must be
-- bounded by the current label and clearance, though the resulting
-- label may not be if the 'Labeled' value's label is already above
-- the current thread's clearance. If the supplied label is not
-- bounded then @taintLabeled@ will throw an exception (see
-- 'guardAlloc').
taintLabeled :: DCLabel -> Labeled DCLabel a -> LIO DCLabel (Labeled DCLabel a)
taintLabeled l (LabeledTCB lold v) = do
  let lnew = lold `lub` l
  withContext "taintLabeled" $ guardAlloc lnew
  state <- getLIOStateTCB
  r <- forM (cToList (dcIntegrity lnew)) $ \goal -> do
    (_, r) <- multiExtract state (cSingleton goal) v
    ioTCB $ wrapRCRef goal r
  return $ LabeledTCB lnew r

-- | Same as 'taintLabeled', but uses privileges when comparing the
-- current label to the supplied label. In other words, this function
-- can be used to lower the label of the labeled value by leveraging
-- the supplied privileges.
taintLabeledP :: DCPriv -> DCLabel -> Transfer a -> Labeled DCLabel a -> LIO DCLabel (Labeled DCLabel a)
taintLabeledP p l t (LabeledTCB lold v) = do
  let lnew = lold `lub` l
  withContext "taintLabeledP" $ guardAllocP p lnew
  state <- getLIOStateTCB
  r <- forM (cToList (dcIntegrity lnew)) $ \goal -> do
    (_, r) <- multiExtractP state p (cSingleton goal) t v
    ioTCB $ wrapRCRef goal r
  return $ LabeledTCB lnew r

{- $functor

Making 'Labeled' an instance of 'Functor' is problematic because:

1. 'fmap' would have type @Labeled l a -> (a -> b) -> Labeled b@ and thus 
    creating /new/ labeled values above the current clearance or below
    the current label would be feasible (given one such value).
2. 'LIO' is polymorphic in the label type and thus 'fmap' would is
   susceptible to /refinement attacks/. Superficially if the label type
   contains an integrity component (see for example "LIO.DCLabel")
   then @fmap (const 3) lv@ would produce a high-integrity labeled @3@
   if @lv@ is a high-integrity labeled value without any any authority
   or /endorsement/.

Similarly, defining an instance of 'Applicative' is an issue.

Instead, we provide 'lFmap' (labeled 'fmap') and 'lAp' that address
the above issues.

-}

-- | A function similar to 'fmap' for 'Labeled' values.  Applies a
-- function to a 'Labeled' value without 'unlabel'ing the value or
-- changing the thread's current label.  The label of the result is the
-- 'lub' of the current label and that of the supplied 'Labeled'
-- value.  Because of laziness, the actual computation on the value of
-- type @a@ will be deferred until a thread with a higher label
-- actually 'unlabel's the result.
lFmap :: Labeled DCLabel a -> (a -> b) -> LIO DCLabel (Labeled DCLabel b)
lFmap (LabeledTCB lold v) f = do
  l <- getLabel
  -- Result label is joined with current label
  let lnew = lold `lub` l
  -- Check for clearance violation
  withContext "lFmap" $ guardAlloc lnew
  -- Apply f, preserving existing structure
  LabeledTCB lnew `fmap` ioTCB (multiFmap lnew f v)


-- Unimplemented for now
-- | Similar to 'ap', apply function (wrapped by 'Labeled') to the
-- labeld value. The label of the returned value is the 'lub' of the
-- thread's current label, the label of the supplied function, and the
-- label of the supplied value.
-- lAp :: Labeled DCLabel (a -> b) -> Labeled DCLabel a -> LIO DCLabel (Labeled DCLabel b)
