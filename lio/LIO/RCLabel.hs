{-# LANGUAGE Trustworthy, ViewPatterns #-}

module LIO.RCLabel where

import LIO.DCLabel
import LIO.TCB
import LIO.Label
import LIO.Error
import LIO.Core

import LIO.RCRef
import LIO.SafeCopy

import safe Data.Map (Map)
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set
import safe Data.Foldable
import safe Data.Maybe
import safe Control.Monad

import Control.Concurrent.MVar
import System.IO.Unsafe

-- In general, interactions with MultiRCRef closely mirrors the
-- corresponding label checks we do, as the label check has an
-- *operational* meaning with respect to how references to resource
-- containers are handled.  So these functions replace the corresponding
-- guards.

-- | Creates a new RCRef mirroring the CNF-structure of the new label.
multiAlloc :: DCLabel -> a -> LIO DCLabel (MultiRCRef a)
multiAlloc newl a = do
  ioTCB $ mkRCRefFromCNF (dcIntegrity newl) a

-- | Creates a new RCRef mirroring the CNF-structure of the new label,
-- copying data into resource containers we have privileges for as
-- necessary.
multiAllocP :: DCPriv -> DCLabel -> Transfer a -> a -> LIO DCLabel (MultiRCRef a)
multiAllocP p newl t a = do
  LIOState { lioLabel = l } <- getLIOStateTCB
  -- Some of the conjuncts may require privilege exercise to be
  -- satisfiable.  The formula we need to provide a construction
  -- for is as follows:
  --
  --    (L1 \/ L2) /\ P1 /\ P2  |=  N1 /\ N2
  --
  -- L = current label, P = privilege, N = new label
  --
  -- By right elimination of conjunction, we can simply solve each
  -- of these statements separately:
  --
  --    (L1 \/ L2) /\ P1 /\ P2  |=  N1
  --    (L1 \/ L2) /\ P1 /\ P2  |=  N2
  --
  -- We prefer to not exercise a privilege when possible
  forM (cToList (dcIntegrity newl)) $ \goal -> do
    -- goal ranges over N1 .. Ni
    a' <- if cImplies1 (dcIntegrity l) goal
            -- L1 \/ L2 |= Ni (no privilege exercise needed)
            -- XXX: Should this also run the transfer function? If we
            -- enforce a partial ordering as part of transfer semantics,
            -- then there is no difficulty as long as we don't force too
            -- much.
            then return a
            -- P1 /\ P2 |= Ni (some privilege is necessary)
            else do
                pd <- maybe (error "multiAllocP: impossible, inconsistent guardAllocP result")
                            return
                            (find (`dImplies` goal) (cToList (privDesc p)))
                -- pd is some Pi such that Pi |= Ni
                rc <- maybe (error "multiAllocP: no underwriter")
                            (ioTCB . principalRC)
                            (dUnderwriter pd)
                -- XXX: As this withRC invocation is not registered with
                -- the runtime, it could block the freeing of a
                -- container.  The proper strategy is to register and
                -- abort if the container goes away.
                ioTCB $ withRC1 rc a (transfer t)
    ioTCB $ wrapRCRef goal a'

-- | Reads out from a MultiRCRef; we may need to taint further than
-- 'taint' did as there may be multiple choices of object source and we
-- can only use one.  Do a smart algorithm to figure out what the
-- optimal choice is (that minimizes final taint).  Needs the old LIOState.
multiTaint :: LIOState DCLabel -> DCLabel -> MultiRCRef a -> LIO DCLabel a
multiTaint old_state newl a = do
    (newl', r) <- multiExtract old_state (dcIntegrity newl) a
    setLabel newl'
    return r

multiExtract :: LIOState DCLabel -> CNF -> MultiRCRef a -> LIO DCLabel (DCLabel, a)
multiExtract old_state newl a = do
    LIOState { lioLabel = l, lioClearance = c } <- getLIOStateTCB
    oldl <- case cToList (dcIntegrity (lioLabel old_state)) of
                [x] -> return x
                [] -> error "multiTaint: current label illegally operating without container"
                _ -> error "multiTaint: current label is conjunction"

    -- We have the following situation:
    --
    -- old current label (from old_state/oldl) = L1 \/ L2 (NB: oldl is a Disjunction)
    -- newl = D1 /\ D2
    -- current label = L1 \/ L2 `lub` D1 /\ D2
    --      NB: this has been factored, so it is not so useful except
    --      to try to figure out if a sub-lub is optimal
    -- new current label = L1 \/ L2 \/ Di
    --      Where Di is chosen to minimize the size of this label.
    --
    -- Ideally, current label `canFlowTo` new current label (this
    -- means no precision loss occurred).
    --
    -- In the event of no optimal choice, we just pick a random ref to
    -- use, since in general there is not a total order.  In fact,
    -- because the CNFs are guaranteed to be in minimal form, there
    -- will be *no* choice that subsumes any of the others.

    -- goal ranges over D1 ... Di
    -- b is the corresponding AnyRCRef for the disjunct
    let search_optimal [] rs = search_first rs
        search_optimal ((goal, b):xs) rs
            -- Check if it is optimal, namely, that the alternate
            -- labeling 'cSingleton (dUnion goal oldl)' can flow
            -- to the chosen dcIntegrity. By construction, the other
            -- flow holds.
            | cSingleton (dUnion goal oldl) `cImplies` dcIntegrity l = do
                mb' <- ioTCB $ readAllRCRef b
                case mb' of
                    Nothing -> search_optimal xs rs
                    Just b' -> return (l, b')
            | otherwise = search_optimal xs ((goal, b):rs)
        -- OK, just go for the first AnyRCRef that works.  Make sure
        -- that it works with the clearance.
        search_first [] = labelError "readMultiRCRef" [l]
        search_first ((goal, b):rs)
            | cSingleton (dUnion goal oldl) `cImplies` dcIntegrity c = do
                mb' <- ioTCB $ readAllRCRef b
                case mb' of
                    Nothing -> search_first rs
                    Just b' -> do
                        return (l { dcIntegrity = cSingleton (dUnion goal oldl) }, b')
            | otherwise = search_first rs

    search_optimal (zip (cToList newl) a) []

-- Similar to multiTaint, but if we can avoid raising the current label
-- by using privileges we will do so. taintP
multiTaintP :: LIOState DCLabel -> DCPriv -> DCLabel -> Transfer a -> MultiRCRef a -> LIO DCLabel a
multiTaintP old_state p newl t a = do
    (newl', r) <- multiExtractP old_state p (dcIntegrity newl) t a
    setLabel newl'
    return r

multiExtractP :: LIOState DCLabel -> DCPriv -> CNF -> Transfer a -> MultiRCRef a -> LIO DCLabel (DCLabel, a)
multiExtractP old_state p newl t a = do
    LIOState { lioLabel = l, lioClearance = c } <- getLIOStateTCB
    oldl <- case cToList (dcIntegrity (lioLabel old_state)) of
                [x] -> return x
                [] -> error "multiTaint: current label illegally operating without container"
                _ -> error "multiTaint: current label is conjunction"

    let -- First, check if we already done, with no privileges necessary
        search_optimal [] rs = search_first rs
        search_optimal ((goal, b):xs) rs
            | cSingleton (dUnion goal oldl) `cImplies` dcIntegrity l = do
                mb' <- ioTCB $ readAllRCRef b
                case mb' of
                    Nothing -> search_optimal xs rs
                    Just b' -> return (l, b')
            | otherwise = search_optimal xs ((goal, b):rs)
        -- Use a privilege to do the transfer
        --  First choice: a privilege such that L1 \/ L2 \/ P  ==  current label;
        --  since current label |= L1 \/ L2 \/ P we just check the other
        --  direction
        best_priv :: Disjunction
        best_priv = fromMaybe (head (cToList (privDesc p))) $
                        find ((`cImplies` dcIntegrity l) . cSingleton . dUnion oldl)
                             (cToList (privDesc p))
        search_first [] = labelError "readMultiRCRef" [l]
        search_first ((goal, b):rs)
            | cSingleton (dUnion goal oldl) `cImplies` dcIntegrity c = do
                mb' <- ioTCB $ readAllRCRef b
                case mb' of
                    Nothing -> search_first rs
                    Just b' -> do
                        rc <- maybe (error "multiAllocP: no underwriter")
                                    (ioTCB . principalRC)
                                    (dUnderwriter best_priv)
                        r <- ioTCB $ withRC1 rc b' (transfer t)
                        return (l { dcIntegrity = cSingleton (dUnion best_priv oldl) }, r)
            | otherwise = search_first rs

    search_optimal (zip (cToList newl) a) []

multiFmap :: DCLabel -> (a -> b) -> MultiRCRef a -> IO (MultiRCRef b)
multiFmap newl f rcref = do
    forM (zip (cToList (dcIntegrity newl)) rcref) $ \(goal, r) -> do
        ma <- readAllRCRef r
        case ma of
            Nothing -> return RCDead
            Just a -> wrapRCRef goal (f a) -- lazy!

--
-- Utility functions
--

-- NB: must be ascending since we'll use this to match up RCRef lists to
-- their corresponding CNFs
cToList :: CNF -> [Disjunction]
cToList = Set.toAscList . cToSet

-- | Create a MultiRCRef based on an arbitrary CNF formula
mkRCRefFromCNF :: CNF -> a -> IO (MultiRCRef a)
mkRCRefFromCNF cnf a = mapM (\d -> wrapRCRef d a) (cToList cnf)

-- | Create an AllRCRef chain based on a disjunction of principals.
wrapRCRef :: Disjunction -> a -> IO (AllRCRef a)
wrapRCRef d a = wrapM (Set.toAscList {- not necessary, but be safe -} (dToSet d)) (RCTerminal a)
    where wrapM [] r = return r
          wrapM (p:ps) r = do
            rc <- principalRC p
            ref <- newRCRef rc r
            wrapM ps (RCGate ref)

-- | Read a value from an AllRCRef chain.
readAllRCRef :: AllRCRef a -> IO (Maybe a)
readAllRCRef (RCTerminal a) = return (Just a)
readAllRCRef RCDead = return Nothing
readAllRCRef (RCGate r) = do
    maybe (return Nothing) readAllRCRef =<< readRCRef r

-- | Attempt to read a value from a MultiRCRef.  May fail if not enough
-- containers are live.
readMultiRCRef :: MultiRCRef a -> IO (Maybe a)
readMultiRCRef [] = return Nothing
readMultiRCRef (r:rs) = do
    maybe (readMultiRCRef rs) (return . Just) =<< readAllRCRef r

--
-- RC management functions
--

-- | Calculate the resource container associated with a principal, or
-- return the "public" container
principalRC :: Principal -> IO RC
principalRC p = withMVar globalPrivMap (\m -> return (fromMaybe (error "principalRC: Uninitialized principal") (Map.lookup p m)))

-- | Global mapping of principals to resource containers
{-# NOINLINE globalPrivMap #-}
globalPrivMap :: MVar (Map Principal RC)
globalPrivMap = unsafePerformIO $ newMVar Map.empty

-- | Initialize some privileges (within the 'IO' monad) that can be
-- passed to 'LIO' computations run with 'runLIO' or 'evalLIO'.  This
-- is a pure function, but the result is encapsulated in 'IO' to
-- make the return value inaccessible from 'LIO' computations.
--
-- [RC] This has an important role of instantiating resource containers
-- for the privileges, so it needs to take a map to maintain the mapping.
privInit :: CNF -> IO (Priv CNF)
privInit p | isPriv p  = fail "privInit called on Priv object"
           | otherwise = do
                parent_rc <- getCurrentRC
                for_ (cToSet p) $ \disj ->
                    for_ (dToSet disj) $ \prin ->
                        modifyMVar_ globalPrivMap $ \m ->
                            case Map.lookup prin m of
                                Nothing -> do
                                    -- allocate a new RC for principal
                                    -- XXX accept some default limit to
                                    -- apply to new principals
                                    rc <- newRC 2000 parent_rc
                                    return (Map.insert prin rc m)
                                Just _ -> return m
                return (PrivTCB p)

-- XXX UGH UGH UGH
labeledTCB :: DCLabel -> a -> Labeled DCLabel a
labeledTCB l a = unsafePerformIO $ do
    LabeledTCB l `fmap` mkRCRefFromCNF (dcIntegrity l) a

unlabelTCB :: Labeled DCLabel a -> (DCLabel, a)
unlabelTCB (LabeledTCB l v) = (l, unsafePerformIO m)
    where m = maybe (error "unlabelTCB oops") return =<< readMultiRCRef v
