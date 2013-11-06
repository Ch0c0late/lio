{-# LANGUAGE MagicHash, UnboxedTuples, UnliftedFFITypes, FlexibleInstances, UndecidableInstances, Unsafe #-}

module LIO.RCRef where

import GHC.Base
import Data.IORef

data RC = RC# RC#
data Listener = Listener# Listener#
data RCRef a = RCRef# (RCRef# a)

getCurrentRC :: IO RC
getCurrentRC = IO $ \s -> case getCurrentRC# () s of (# s', rc' #) -> (# s', RC# rc' #)

newRC :: Word -> RC -> IO RC
newRC (W# w) (RC# rc) = IO $ \s -> case newRC# w rc s of (# s', rc' #) -> (# s', RC# rc' #)

withRC :: RC -> IO a -> IO a
withRC (RC# rc) (IO m) = IO $ \s -> withRC# rc m s

-- fake it till you make it
withRC1 :: RC -> a -> (a -> IO b) -> IO b
withRC1 rc x f = do
    rx <- newIORef x
    withRC rc $ readIORef rx >>= f

-- XXX should be Word
listenRC :: RC -> Int -> IO () -> IO Listener
listenRC (RC# rc) (I# w) cb = IO $ \s -> case listenRC# rc w cb s of (# s', l #) -> (# s', Listener# l #)

unlistenRC :: Listener -> IO ()
unlistenRC (Listener# l) = IO $ \s -> unlistenRC# l s

readRCRef :: RCRef a -> IO (Maybe a)
readRCRef (RCRef# ref) = IO $ \s -> case readRCRef# ref s of
    (# s' , r , p #) -> case r of
        1# -> (# s', Just p #)
        _ -> (# s', Nothing #)

newRCRef :: RC -> a -> IO (RCRef a)
newRCRef (RC# rc) p = IO $ \s -> case newRCRef# rc p s of (# s' , r #) -> (# s' , RCRef# r #)
