module McCarthy91 where

import Tip

--------------------------------------------------------------------------------

m :: Int -> Int
m n | n > 100   = n-10
    | otherwise = m (m (n+11))

--------------------------------------------------------------------------------

prop_M1 n =
  n <= 100 === True ==> m n === 91

prop_M2 n =
  n >= 101 === True ==> m n === n-10

