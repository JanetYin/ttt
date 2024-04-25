open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool

_×_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A × B = Σ A λ _ → B
infixr 4 _×_

data _⊎_ {ℓ κ}(A : Set ℓ)(B : Set κ) : Set (ℓ ⊔ κ) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

case : ∀{ℓ κ μ}{A : Set ℓ}{B : Set κ}{C : Set μ} → A ⊎ B → (A → C) → (B → C) → C
case (inl a) f _ = f a
case (inr b) _ g = g b

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

¬_ : ∀{ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥
infixr 5 ¬_

exfalso : ∀{ℓ}{A : Set ℓ} → ⊥ → A
exfalso ()

{-

Useful keybinds
M = Alt
C = Control

M-w = Copy
C-w = Cut
C-y = Paste
C-x h = Select entire file
C-x C-f = Open file
C-c C-l = Load file
C-c C-, = Show goal type
C-c C-SPC = Put expr in hole
C-c C-r = Put expr in hole or introduce trivial constructor
C-c C-c RETURN = Put parameters before equality sign
C-c C-c <varname> RETURN = Pattern match of <varname>
C-c C-x C-q or C-c C-x C-r = Kill Agda
C-u C-u C-c C-, (Emacs) or C-y C-c C-, (VSCode) = Show fully normalized goal type

-}

-- Prove that the following first order logical expression is false for some universe and predicates
ex : ¬ ((A : Set)(R : A → A → Set) → ((a : A)(b : A)(c : A) → R a b → R b c → R a c) → (a : A)(b : A) → R a b → R b a)
ex x with x Bool R p1 false true tt
  where
    R : Bool → Bool → Set
    R false c = ⊤
    R true false = ⊥
    R true true = ⊤
    p1 : (a : Bool)(b : Bool)(c : Bool) → R a b → R b c → R a c
    p1 false b c x x₁ = tt
    p1 true true c x x₁ = x₁
... | ()
