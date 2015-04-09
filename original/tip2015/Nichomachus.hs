module Nichomachus where

import Prelude (error)
import Nat hiding (sig)
import Tip.DSL
import Test.QuickCheck hiding ((==>))
import Data.Typeable
import QuickSpec.Signature

sum :: Nat -> Nat
sum Z     = Z
sum (S n) = sum n + S n

cubes :: Nat -> Nat
cubes Z     = Z
cubes (S n) = cubes n + (S n * S n * S n)

prop_theorem :: Nat -> Prop Nat
prop_theorem n = cubes n =:= sum n * sum n
