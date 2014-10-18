module Prob03 where

open import Data.Nat
open import Data.Fin using (toℕ)
open import Data.Vec hiding (_>>=_)
open import Coinduction
open import Data.Stream as Stream
open import Function
open import Data.Maybe as Maybe

open import Level renaming (suc to lsuc ; zero to lzero)
open import Category.Monad
open RawMonad (Maybe.monad {Level.zero})

nats : Stream ℕ
nats = iterate suc zero

solution-space : Stream (Maybe ℕ)
solution-space = Stream.map just $ Stream.drop 2 nats

cycle : ∀ {n} {A : Set} → Vec A (suc n) → Stream A
cycle {A = A} (x ∷ xs) = x ∷ ♯ aux xs
  where
  aux : ∀ {n} → Vec A n → Stream A
  aux [] = x ∷ ♯ (aux xs)
  aux (x₁ ∷ xs') = x₁ ∷ ♯ aux xs'

_⊛∞_ : {A B : Set} → Stream (A → B) → Stream A → Stream B
(f ∷ fs) ⊛∞ (a ∷ as) = f a ∷ ♯ (♭ fs ⊛∞ ♭ as)

sieve : ℕ → Stream (Maybe ℕ → Maybe ℕ)
sieve zero = repeat id
sieve (suc n) = cycle (tabulate {n} (λ _ → id) ∷ʳ const nothing)

sieve-step : (n : ℕ) → Stream (Maybe ℕ) → Stream (Maybe ℕ)
sieve-step n xs = (sieve n) ⊛∞ xs

primes : Stream (Maybe ℕ)
primes = aux solution-space
  where
  aux : Stream (Maybe ℕ) → Stream (Maybe ℕ)
  aux (x ∷ xs) with x
  ... | just n  = x ∷ ♯ (aux (sieve-step n (♭ xs)))
  ... | nothing = x ∷ ♯ (aux (♭ xs))
