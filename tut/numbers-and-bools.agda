module tut.numbers-and-bools where

open import lib

_+_ : ℕ → (ℕ → ℕ)
_+_ = λ x → rec x suc

_*_ : ℕ → (ℕ → ℕ)
_*_ = λ x → rec 0 (λ z → z + x)

_^_ : ℕ → (ℕ → ℕ)
_^_ = λ x → rec 1 (λ z → z * x)

is0 : ℕ → Bool
is0 = rec true (λ _ → false)

not : Bool → Bool
not = λ x → if x then false else true

and : Bool → Bool → Bool
and = λ x y → if x then y else false

or : Bool → Bool → Bool
or = λ x y → if x then true else y

pred : ℕ → ℕ
pred = λ n → proj₂ (rec {A = ℕ × ℕ} ( 0 , 0) (λ p → suc (proj₁ p) , proj₁ p) n)

eq : ℕ → ℕ → Bool
eq = rec is0 (λ isn-1 n → and (isn-1 (pred n)) (not (isn-1 n)))

