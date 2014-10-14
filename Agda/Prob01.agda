module Prob01 where

open import Coinduction
open import Data.Nat
open import Data.Stream as Stream
open import Data.Vec

module Prob01 where
  open import Data.Bool
  open import Data.Nat.Divisibility
  open import Relation.Nullary.Decidable
  open import Data.Fin using (toℕ)
  open import Relation.Binary.PropositionalEquality

  nats : Stream ℕ
  nats = iterate suc zero

  repeat-Vec : ∀ {n} {A : Set} → Vec A (suc n) → Stream A
  repeat-Vec {A = A} (x ∷ xs) = x ∷ ♯ aux xs
    where
      aux : ∀ {m} → Vec A m → Stream A
      aux [] = x ∷ ♯ aux xs
      aux (x' ∷ xs') = x' ∷ ♯ aux xs'

  div3∨5-tab = tabulate {3 * 5} (λ i → let n = toℕ i in ⌊ 3 ∣? n ⌋ ∨ ⌊ (5 ∣? n) ⌋)
  div3∨5-hcv : Vec Bool _
  div3∨5-hcv = true ∷ false ∷ false ∷ true ∷ false ∷ true ∷ true ∷ false ∷ false ∷ true ∷ true ∷ false ∷ true ∷ false ∷ false ∷ []

  div3∨5-≡ : div3∨5-tab ≡ div3∨5-hcv
  div3∨5-≡ = refl

  div3∨5 : Stream Bool
  div3∨5 = repeat-Vec div3∨5-hcv

  terms = Stream.zipWith (λ n div? → if div? then n else 0) nats div3∨5

  solution : ℕ → ℕ
  solution n = sum (Stream.take n terms)

module Friend where
  merge-multiples : Stream ℕ → Stream ℕ → Stream ℕ
  merge-multiples (x ∷ xs) (y ∷ ys) with compare x y
  merge-multiples (x ∷ xs) (.(suc (x + k)) ∷ ys) | less .x k =
    x ∷ ♯ merge-multiples (♭ xs) (suc (x + k) ∷ ys)
  merge-multiples (x ∷ xs) (.x ∷ ys) | equal .x =
    x ∷ ♯ merge-multiples (♭ xs) (♭ ys)
  merge-multiples (.(suc (y + k)) ∷ xs) (y ∷ ys) | greater .y k =
    y ∷ ♯ merge-multiples (suc (y + k) ∷ xs) (♭ ys)

  multiples : ℕ → Stream ℕ
  multiples n = iterate (_+_ n) zero

  threes = multiples 3
  fives  = multiples 5
  threes-and-fives = merge-multiples threes fives

  terms = Stream.take 467 threes-and-fives
