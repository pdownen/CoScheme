{-# OPTIONS --guardedness #-}
module Streams where

open import Data.Nat

record Stream (a : Set) : Set where
  coinductive
  constructor _,_
  field
    Head : a
    Tail : Stream a
open Stream

zipWith : ∀ {a b c} → (a → b → c) → Stream a → Stream b → Stream c
Head (zipWith f xs ys) = f (Head xs) (Head ys)
Tail (zipWith f xs ys) = zipWith f (Tail xs) (Tail ys)

-- The termination checker doesn't believe this is well-founded corecursion
{-
fibs : Stream ℕ
Head fibs = 0
Head (Tail fibs) = 1
Tail (Tail fibs) = zipWith _+_ fibs (Tail fibs)
-}

-- An alternate version that remembers the previous two numbers

fibsFrom : ℕ → ℕ → Stream ℕ
Head (fibsFrom x y)        = x
Head (Tail (fibsFrom x y)) = y
Tail (Tail (fibsFrom x y)) = fibsFrom y (x + y)

fibs : Stream ℕ
fibs = fibsFrom 0 1

