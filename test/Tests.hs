import Test.Tasty (defaultMain, TestTree, testGroup)

import Crypto

import Test.Tasty.HUnit (testCase, (@?=), Assertion, HasCallStack)

import Prelude hiding (subtract, gcd)

-- run with `cabal test --test-options="--color always"` for colour if desired
main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "crypto"
  [ testGroup "part 1"
      [ testGroup "gcd" (numberedTests gcdTests)
      , testGroup "phi" (numberedTests phiTests)
      , testGroup "modPow" (numberedTests modPowTests)
      , testGroup "computeCoeffs" (numberedTests computeCoeffsTests)
      , testGroup "inverse" (numberedTests inverseTests)
      , testGroup "smallestCoPrimeOf" (numberedTests smallestCoPrimeOfTests)
      , testGroup "genKeys" (numberedTests genKeysTests)
      , testGroup "rsaEncrypt" (numberedTests rsaEncryptTests)
      , testGroup "rsaDecrypt" (numberedTests rsaDecryptTests)
      ]
  , testGroup "part 2"
      [ testGroup "toInt" (numberedTests toIntTests)
      , testGroup "toChar" (numberedTests toCharTests)
      , testGroup "add" (numberedTests addTests)
      , testGroup "subtract" (numberedTests subtractTests)
      , testGroup "ecbEncrypt" (numberedTests ecbEncryptTests)
      , testGroup "ecbDecrypt" (numberedTests ecbDecryptTests)
      , testGroup "cbcEncrypt" (numberedTests cbcEncryptTests)
      , testGroup "cbcDecrypt" (numberedTests cbcDecryptTests)
      ]
  -- you can feel free to add your own test group here!
  ]

-------------------------------------------------------------------------------
-- PART 1 : asymmetric encryption

gcdTests :: [Assertion]
gcdTests = [ gcd 0 0      --> 0  -- gcd.#1
           , gcd 0 8      --> 8  -- gcd.#2
           , gcd 8 0      --> 8  -- gcd.#3
           , gcd 3 3      --> 3  -- gcd.#4
           , gcd 12 16    --> 4  -- gcd.#5
           , gcd 16 12    --> 4  -- gcd.#6
           , gcd 65 40    --> 5  -- gcd.#7
           , gcd 735 1239 --> 21 -- gcd.#8
           , gcd 128 65536 --> 128
           ]

phiTests :: [Assertion]
phiTests = [ phi 0  --> 0
           , phi 1  --> 1
           , phi 2  --> 1
           , phi 6  --> 2
           , phi 18 --> 6
           , phi 17 --> 16
           , phi 31 --> 30
           , phi 35 --> 24
           , phi 77 --> 60
           , phi 12 --> 4
           ]

modPowTests :: [Assertion]
modPowTests = [ modPow 0 0 1                   --> 0
              , modPow 1 1 1                   --> 0
              , modPow 1 1 2                   --> 1
              , modPow 13481 11237 6           --> 5
              , modPow 8 0 1                   --> 0
              , modPow 8 0 5                   --> 1
              , modPow 237 1 1000              --> 237
              , modPow 859237 1 1000           --> 237
              , modPow 33893 2 10000           --> 5449
              , modPow 7433893 2 10000         --> 5449
              , modPow 13481503 11237126 46340 --> 6629
              , modPow 2 31 10 --> 8
              ]

computeCoeffsTests :: [Assertion]
computeCoeffsTests = [ computeCoeffs 0 0      --> (1, 0)
                     , computeCoeffs 0 8      --> (0, 1)
                     , computeCoeffs 12 16    --> (-1, 1)
                     , computeCoeffs 16 12    --> (1, -1)
                     , computeCoeffs 65 40    --> (-3, 5)
                     , computeCoeffs 735 1239 --> (27, -16)
                     , computeCoeffs 13 14 --> (-1,1)
                     ]

inverseTests :: [Assertion]
inverseTests = [ inverse 11 16 --> 3
               , inverse 4 15  --> 4
               , inverse 18 35 --> 2
               , inverse 35 18 --> 17
               , inverse 12 91 --> 38
               , inverse 34 91 --> 83
               , inverse 64 91 --> 64
               , inverse 3 11 --> 4
               ]

smallestCoPrimeOfTests :: [Assertion]
smallestCoPrimeOfTests = [ smallestCoPrimeOf 1   --> 2
                         , smallestCoPrimeOf 2   --> 3
                         , smallestCoPrimeOf 12  --> 5
                         , smallestCoPrimeOf 13  --> 2
                         , smallestCoPrimeOf 30  --> 7
                         , smallestCoPrimeOf 210 --> 11
                         , smallestCoPrimeOf 15 --> 2
                         ]

genKeysTests :: [Assertion]
genKeysTests = [ genKeys 2 3         --> ((3,6),(1,6))
               , genKeys 17 23       --> ((3,391),(235,391))
               , genKeys 101 83      --> ((3,8383),(5467,8383))
               , genKeys 401 937     --> ((7,375737),(213943,375737))
               , genKeys 613 997     --> ((5,611161),(243821,611161))
               , genKeys 26641 26437 --> ((7,704308117),(100607863,704308117))
               , genKeys 5 11 --> ((3,55),(27,55))
               ]

rsaEncryptTests :: [Assertion]
rsaEncryptTests = [ rsaEncrypt 4321 (3,8383)            --> 3694
                  , rsaEncrypt 324561 (5, 611161)       --> 133487
                  , rsaEncrypt 1234 (5,611161)          --> 320878
                  , rsaEncrypt 704308111 (7, 704308117) --> 704028181
                  , rsaEncrypt 7 (3,55) --> 13
                  ]

rsaDecryptTests :: [Assertion]
rsaDecryptTests = [ rsaDecrypt 3694 (5467,8383)                --> 4321
                  , rsaDecrypt 133487 (243821,611161)          --> 324561
                  , rsaDecrypt 320878 (243821,611161)          --> 1234
                  , rsaDecrypt 704028181 (100607863,704308117) --> 704308111
                  , rsaDecrypt 13 (27,55) --> 7
                  ]

-------------------------------------------------------------------------------
-- PART 2 : symmetric encryption


toIntTests :: [Assertion]
toIntTests = [ toInt 'a' --> 0
             , toInt 'z' --> 25
             , toInt 'h' --> 7
             , toInt 'f' --> 5
             ]

toCharTests :: [Assertion]
toCharTests = [ toChar 0  --> 'a'
              , toChar 25 --> 'z'
              , toChar 7  --> 'h'
              , toChar 5 --> 'f'
              ]

addTests :: [Assertion]
addTests = [ add 'a' 'a' --> 'a'
           , add 'd' 's' --> 'v'
           , add 'w' 't' --> 'p'
           , add 'z' 'g' --> 'f'
           ]

subtractTests :: [Assertion]
subtractTests = [ subtract 'a' 'a' --> 'a'
                , subtract 'v' 's' --> 'd'
                , subtract 'p' 'w' --> 't'
                , subtract 'f' 'g' --> 'z'
                 ]

ecbEncryptTests :: [Assertion]
ecbEncryptTests = [ ecbEncrypt 'w' ""        --> ""
                  , ecbEncrypt 'd' "w"       --> "z"
                  , ecbEncrypt 'x' "bonjour" --> "ylkglro"
                  , ecbEncrypt 'k' "hello"   --> "rovvy"
                  , ecbEncrypt 'b' "hello"   --> "ifmmp"
                  ]

ecbDecryptTests :: [Assertion]
ecbDecryptTests = [ ecbDecrypt 'w' ""        --> ""
                  , ecbDecrypt 'd' "z"       --> "w"
                  , ecbDecrypt 'x' "ylkglro" --> "bonjour"
                  , ecbDecrypt 'k' "rovvy"   --> "hello"
                  , ecbDecrypt 'b' "ifmmp"   --> "hello"
                  ]

cbcEncryptTests :: [Assertion]
cbcEncryptTests = [ cbcEncrypt 'w' 'i' ""        --> ""
                  , cbcEncrypt 'd' 'i' "w"       --> "h"
                  , cbcEncrypt 'x' 'w' "bonjour" --> "ufpvgxl"
                  , cbcEncrypt 'k' 'q' "hello"   --> "hvqlj"
                  , cbcEncrypt 'a' 'b' "ciao" --> "dllz"
                  ]

cbcDecryptTests :: [Assertion]
cbcDecryptTests = [ cbcDecrypt 'w' 'i' ""        --> ""
                  , cbcDecrypt 'd' 'i' "h"       --> "w"
                  , cbcDecrypt 'x' 'w' "ufpvgxl" --> "bonjour"
                  , cbcDecrypt 'k' 'q' "hvqlj"   --> "hello"
                  , cbcDecrypt 'a' 'b' "dllz" --> "ciao"
                  ]

-------------------------------------------------------------------------------
-- HELPERS

{-|
This function ensures that its first argument is the same as the second one
-}
infix 1 -->
(-->) :: (Show a, Eq a, HasCallStack)
      => a -- ^ the actual value
      -> a -- ^ the expected value
      -> Assertion
(-->) = (@?=)

{-|
This function just matches up a bunch of assertions to a numerical naming system, allowing us to distinguish them.

If we wanted, we could provide descriptions to them instead...
-}
numberedTests :: [Assertion] -> [TestTree]
numberedTests = zipWith (\n -> testCase ("#" ++ show n)) ([1..] :: [Integer])
