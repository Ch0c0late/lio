module LIO.RingSig
       ( sign
       , verify
       , RingSig(..)
       ) where


import Crypto.PubKey.RSA
import Crypto.PubKey.RSA.Prim as RSA
import Crypto.Random.API
import Crypto.Cipher.AES
import Crypto.Hash.SHA256 (hash)
import Crypto.Number.Serialize (os2ip, i2osp)

import qualified Data.ByteString as B
import Data.Bits (xor)

type RingSig = ([PublicKey], B.ByteString, [B.ByteString])

xorString :: B.ByteString -> B.ByteString -> B.ByteString
xorString x y = B.pack  (B.zipWith xor x y)

{- Combining Function -}
c :: Key ->  B.ByteString -> [B.ByteString] -> B.ByteString
c key v ys = foldl (\y1 y2 -> (encryptECB key (xorString y1 y2))) v ys

{- Inverse of above function, used to solve for signer's y_s -}
cinv :: Key -> B.ByteString -> [B.ByteString] -> B.ByteString
cinv key v ys = decryptECB key (foldr (\y1 y2 -> xorString (decryptECB key y2) y1) v ys)


{- Extended trapdoor permutation to common domain 512 bits larger than biggest key -}
extended_trapdoor :: PublicKey -> B.ByteString -> Int -> B.ByteString
extended_trapdoor k x l 
  = let q = (os2ip x) `quot` (public_n k)
        r = (os2ip x) `mod` (public_n k)
        n = public_n k
    in case () of
      _ | (q+1) * n <= 2^(l + 512) -> i2osp (q*n + (os2ip (RSA.ep k (i2osp r))))
        | otherwise -> i2osp(0)

{- Inverse for extended trapdoor -}
extended_trapdoorInv :: PrivateKey -> B.ByteString -> Int -> B.ByteString
extended_trapdoorInv k x l
  = let n = public_n (private_pub k)
        q = (os2ip x) `quot` n
        r = (os2ip x) `mod`  n
    in case () of
      _ | (q+1) * n <= 2^(l + 512) -> i2osp (q*n + (os2ip (RSA.dp Nothing k (i2osp r))))
        | otherwise -> i2osp(0)

{- Generates a list of num random ByteStrings each of length l -}
genList :: (CPRG g, Num n, Eq n) => g-> n -> Int -> [B.ByteString] -> ([B.ByteString], g)
genList g num l ret
  | num == 0 = (ret, g)
  | otherwise = genList g' (num - 1) l (rand:ret)
                where (rand, g') = genRandomBytes l g
                      
{- Maximum key size in bits of all keys in the ring -}
getLargestKey :: [PublicKey] -> Maybe PrivateKey -> Int
getLargestKey pks Nothing   = 8 * (foldl (\cur curmax -> max cur curmax) 0 sizes)
  where
    sizes = map (\key -> public_size key) pks
getLargestKey pks (Just sk) = 8 * (max privsize (foldl (\cur curmax -> max cur curmax) 0 sizes))
  where
    sizes = map (\key -> public_size key) pks
    privsize = public_size(private_pub sk)


sign :: CPRG g => g -> B.ByteString -> [PublicKey] -> PrivateKey -> Int -> RingSig
sign g m pks sk index = 
  let k = hash m
      l = getLargestKey pks (Just sk)
      (v, g1) = genRandomBytes (l `div` 8) g
      (xs,g2) = genList g1 (length pks) (l `div` 8) []
      ys = map (\(pk, x) -> extended_trapdoor pk x l) (zip pks xs)
      (xpre, xpost) = splitAt (index - 1) xs
      (ypre, ypost) = splitAt (index - 1) ys
      (pkpre, pkpost) = splitAt (index - 1) pks
      partial = c (initKey k) v ypre 
      reverse = cinv (initKey k) v ypost
      ysk = xorString partial reverse
      xsk = extended_trapdoorInv sk ysk l
      in (pkpre ++ [(private_pub sk)] ++ pkpost, v, xpre ++ [xsk] ++ xpost)
                  
verify :: RingSig -> B.ByteString -> Bool
verify (pks, v, xs) m =
  let k = hash m
      l = getLargestKey pks Nothing
      ys = map (\(pk, x) -> extended_trapdoor pk x l) (zip pks xs)
      ckv = c (initKey k) v ys
      in ckv == v