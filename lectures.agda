module lectures where

open import lib

not : Bool → Bool
not = λ x → if x then false else true

plus : ℕ → ℕ → ℕ
plus = λ x y → primrec y (λ _ n → suc n) x

eq : ℕ → ℕ → Bool
eq = λ x → primrec is0 (λ _ → f) x
  where
    is0 : ℕ → Bool
    is0 = λ y → primrec true (λ _ _ → false) y
    f : (ℕ → Bool) → (ℕ → Bool)
    f = λ isn → λ y → primrec false (λ y' _ → isn y') y

eqb : Bool → Bool → Bool
eqb = λ x y → if x then y else not y

Eqb : Bool → Bool → Set
Eqb = λ x y → if x then (if y then ⊤ else ⊥) else (if y then ⊥ else ⊤)

notUnitTest : Eqb (not (not true)) true
notUnitTest = tt

notInvolutive : (x : Bool) → Eqb (not (not x)) x
notInvolutive = λ x → indBool (λ y → Eqb (not (not y)) y) tt tt x

Eqn : ℕ → ℕ → Set
Eqn = λ x y → Eqb (eq x y) true

testEqnZero : Eq Set (Eqn zero zero) ⊤
testEqnZero = refl

testEqnSuc : {x y : ℕ} → Eq Set (Eqn (suc x) (suc y)) (Eqn x y)
testEqnSuc = refl

plusLeftId : (x : ℕ) → Eqn (plus zero x) x
plusLeftId = λ x → indℕ (λ x → Eqn x x) tt (λ _ e → e) x

plusRightId : (x : ℕ) → Eqn (plus x zero) x
plusRightId = λ x → indℕ (λ x → Eqn (plus x zero) x) tt (λ _ e → e) x
