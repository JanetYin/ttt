module SK.b where

open import Data.Nat
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Vec

postulate
  Tm  : Set
  _·_ : Tm → Tm → Tm
  S K I B : Tm

infixl 5 _·_ _·s_

variable
  t u v w : Tm

postulate
  Iβ : I · u ≡ u
  Kβ : K · u · v ≡ u
  Bβ : B · t · u · v ≡ t · (u · v)

-- I = S · K · K
-- B = S · (K · S) · K

_·s_ : Tm → {n : ℕ} → Vec Tm n → Tm
_·s_ t {zero}  [] = t
_·s_ t {suc n} (u ∷ us)  = t · u ·s us

proj : (n : ℕ) → Fin n → Tm
proj (suc zero)    zero    = I
proj (suc (suc n)) zero    = B · K · proj (suc n) zero
proj (suc (suc n)) (suc x) = K · proj (suc n) x

projβ : (n : ℕ)(x : Fin n)(us : Vec Tm n) → proj n x ·s us ≡ lookup us x
projβ (suc zero)    zero    (u ∷ [])      = Iβ
projβ (suc (suc n)) zero    (u ∷ u' ∷ us) = trans (cong (λ z → z · u' ·s us) Bβ) (trans (cong (_·s us) Kβ) (projβ (suc n) zero (u ∷ us)))
projβ (suc (suc n)) (suc x) (u ∷ u' ∷ us) = trans (cong (λ x → x · u' ·s us) Kβ) (projβ (suc n) x (u' ∷ us))
