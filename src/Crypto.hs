module Crypto ( gcd, smallestCoPrimeOf, phi, phialt, computeCoeffs, inverse
              , modPow, genKeys, rsaEncrypt, rsaDecrypt, toInt, toChar
              , add, subtract, ecbEncrypt, ecbDecrypt
              , cbcEncrypt, cbcDecrypt ) where

import Data.Char

import Prelude hiding (gcd, subtract)
import Control.Monad.ST.Lazy (strictToLazyST)

{-
The advantage of symmetric encryption schemes like AES is that they are efficient
and we can encrypt data of arbitrary size. The problem is how to share the key.
The flaw of the RSA is that it is slow and we can only encrypt data of size lower
than the RSA modulus n, usually around 1024 bits (64 bits for this exercise!).

We usually encrypt messages with a private encryption scheme like AES-256 with
a symmetric key k. The key k of fixed size 256 bits for example is then exchanged
via the aymmetric RSA.
-}

-------------------------------------------------------------------------------
-- PART 1 : asymmetric encryption

-- | Returns the greatest common divisor of its two arguments
gcd :: Int -> Int -> Int
gcd n m
  | m == 0 = n
  | otherwise = gcd m (n `mod` m)

-- | Euler Totient function
phi :: Int -> Int
phi m = length [x | x <-[1..m], gcd m x == 1]

-- | Alternative method
phialt :: Int -> Int
phialt m = cntCoPrime (m - 1)
  where
    cntCoPrime n
      |  n == 1 = 1
      |  gcd m n == 1 = cntCoPrime (n - 1) + 1
      |  otherwise = cntCoPrime (n - 1)

{-|
Calculates (u, v, d) the gcd (d) and Bezout coefficients (u and v)
such that au + bv = d
-}
computeCoeffs :: Int -> Int -> (Int, Int)
computeCoeffs a b
  | b == 0 = (1,0)
  | otherwise =
    let (q,r) = quotRem a b
        (us,vs) = computeCoeffs b r
        in (vs,us - q * vs)

-- | Inverse of a modulo m
inverse :: Int -> Int -> Int
inverse a m
  | gcd a m /= 1 = error "inverse modulo does not exist"
  | otherwise =
    let (u,_) = computeCoeffs a m
        in u `mod` m

-- | Calculates (a^k mod m)
modPow :: Int -> Int -> Int -> Int
modPow a k m
  | m == 1 = 0
  | k == 0 = 1
  | even k = modPow ((a ^ 2) `mod` m) (k `div` 2) m
  | otherwise = (a * modPow a (k - 1) m) `mod` m

-- | Returns the smallest integer that is coprime with phi
smallestCoPrimeOf :: Int -> Int
smallestCoPrimeOf a = testCoPrime 2
  where
    testCoPrime n
      | gcd a n == 1 = n
      | otherwise = testCoPrime (n + 1)

{-|
Generates keys pairs (public, private) = ((e, n), (d, n))
given two "large" distinct primes, p and q
-}
genKeys :: Int -> Int -> ((Int, Int), (Int, Int))
genKeys p q =
  let n = p*q
      e = finde 2
      d = inverse e ((p-1) * (q-1))
      in ((e,n),(d,n))
      where
        finde i
          | gcd i ((p-1) * (q-1)) == 1 = i
          | otherwise = finde (i+1)

-- | This function performs RSA encryption
rsaEncrypt :: Int        -- ^ value to encrypt
           -> (Int, Int) -- ^ public key
           -> Int
rsaEncrypt x (e,n) = modPow x e n

-- | This function performs RSA decryption
rsaDecrypt :: Int        -- ^ value to decrypt
           -> (Int, Int) -- ^ public key
           -> Int
rsaDecrypt c (d,n) = modPow c d n

-------------------------------------------------------------------------------
-- PART 2 : symmetric encryption

-- | Returns position of a letter in the alphabet
toInt :: Char -> Int
toInt c = ord c - ord 'a'

-- | Returns the n^th letter
toChar :: Int -> Char
toChar n = chr (ord 'a' + n)

-- | "adds" two letters
add :: Char -> Char -> Char
add a b = toChar (overflow (toInt a + toInt b))
  where overflow n
          | n > 25 = n - 26
          | n < 0 = n + 26
          | otherwise = n

-- | "subtracts" two letters
subtract :: Char -> Char -> Char
subtract a b = toChar (overflow (toInt a - toInt b))
  where overflow n
          | n > 25 = n - 26
          | n < 0 = n + 26
          | otherwise = n

-- the next functions present
-- 2 modes of operation for block ciphers : ECB and CBC
-- based on a symmetric encryption function e/d such as "add"

-- | ecb (electronic codebook) encryption with block size of a letter
ecbEncrypt :: Char -> [Char] -> [Char]
ecbEncrypt _ [] = []
ecbEncrypt k (c : m) = add c k : ecbEncrypt k m

-- | ecb (electronic codebook) decryption with a block size of a letter
ecbDecrypt :: Char -> [Char] -> [Char]
ecbDecrypt _ [] = []
ecbDecrypt k (c : m) = subtract c k : ecbDecrypt k m

-- | cbc (cipherblock chaining) encryption with block size of a letter
cbcEncrypt :: Char   -- ^ public key
           -> Char   -- ^ initialisation vector `iv`
           -> [Char] -- ^ message `m`
           -> [Char]
cbcEncrypt _ _ [] = []
cbcEncrypt k iv (x : m) = 
  let c = add (add x iv) k
  in c : cbcEncrypt k c m

-- | cbc (cipherblock chaining) decryption with block size of a letter
cbcDecrypt :: Char   -- ^ private key
           -> Char   -- ^ initialisation vector `iv`
           -> [Char] -- ^ message `m`
           -> [Char]
cbcDecrypt _ _ [] = []
cbcDecrypt k iv (c : m) = 
  let x = subtract (subtract c k) iv
  in x : cbcDecrypt k c m
