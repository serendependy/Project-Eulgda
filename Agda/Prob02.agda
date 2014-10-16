module Prob02 where

open import Data.Nat
open import Coinduction
open import Data.Stream as Stream
open import Data.Vec as Vec
open import Data.Product
open import Function

data Parity : Set where
  even odd : Parity

sucₚ : Parity → Parity
sucₚ even = odd
sucₚ odd = even

_+ₚ_ : (p q : Parity) → Parity
even +ₚ q = q
odd +ₚ q = sucₚ q

module Proofs where
  open import Data.Nat.Properties.Simple
  open import Relation.Binary.PropositionalEquality

  data ParityI : ℕ → Set where
    even : ∀ n → ParityI (n * 2)
    odd  : ∀ n → ParityI (1 + n * 2)

  parity : ∀ n → ParityI n
  parity zero = even zero
  parity (suc n) with parity n
  parity (suc .(n * 2))       | even n = odd n
  parity (suc .(suc (n * 2))) | odd n = even (suc n)

  parity-+ : ∀ {m n} → ParityI m → ParityI n → ParityI (m + n)
  parity-+ (even n) (even n₁) rewrite sym $ distribʳ-*-+ 2 n n₁ = even (n + n₁)
  parity-+ (even n) (odd n₁)  rewrite +-suc (n * 2) (n₁ * 2) 
                              |       sym $ distribʳ-*-+ 2 n n₁ = odd (n + n₁)
  parity-+ (odd n)  (even n₁) rewrite sym $ distribʳ-*-+ 2 n n₁ = odd (n + n₁)
  parity-+ (odd n)  (odd n₁)  rewrite +-suc (n * 2) (n₁ * 2)
                              | sym $ distribʳ-*-+ 2 n n₁ = even (suc (n + n₁))

  toParity : ∀ {n} → ParityI n → Parity
  toParity (even n) = even
  toParity (odd n) = odd

  +ₚ-correct : ∀ {m n} → (pₘ : ParityI m) → (pₙ : ParityI n) → toParity (parity-+ pₘ pₙ) ≡ (toParity pₘ) +ₚ (toParity pₙ)
  +ₚ-correct (even n) (even n₁) rewrite sym $ distribʳ-*-+ 2 n n₁ = refl
  +ₚ-correct (even n) (odd n₁)  rewrite +-suc (n * 2) (n₁ * 2) 
                                |       sym $ distribʳ-*-+ 2 n n₁ = refl
  +ₚ-correct (odd n) (even n₁)  rewrite sym $ distribʳ-*-+ 2 n n₁ = refl
  +ₚ-correct (odd n) (odd n₁)   rewrite +-suc (n * 2) (n₁ * 2)
                                | sym $ distribʳ-*-+ 2 n n₁ = refl

open Proofs using (parity ; toParity)

fibs-gen : (m n : ℕ) → Stream ℕ
fibs-gen m n = m ∷ ♯ fibs-gen n (m + n)

fibs : Stream ℕ
fibs = fibs-gen 1 2

fibs-parity : Stream Parity
fibs-parity with Vec.map (toParity ∘ parity) $ Stream.take 2 fibs
fibs-parity | p₁ ∷ p₂ ∷ [] = p₁ ∷ ♯ aux p₂ (p₁ +ₚ p₂)
  where
  aux : (p q : Parity) → Stream Parity
  aux p' q' = p' ∷ ♯ (aux q' (p' +ₚ q'))

fibs-tagged : Stream (ℕ × Parity)
fibs-tagged = Stream.zipWith _,_ fibs fibs-parity

solution : ℕ → ℕ
solution n = sum $ Vec.map (λ { (n₁ , even) → n₁ ; (n₁ , odd) → 0 }) $ Stream.take n fibs-tagged

