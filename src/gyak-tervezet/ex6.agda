module ex6 where

open import Lib 



Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ A B R x y = fst x  , snd x y 

AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC A B R x = (λ x₁ → fst (x x₁)) , λ x₁ → snd (x x₁)


P01 : {A B : Set} {R : A → B → Set} → ((x : A) → (Σ B (λ y → R x y))) → (Σ (A → B) λ f → (x : A) → R x (f x)) --same as Σ B λ y → (x : A) → R x y?
fst (P01 x) x₁ = {!   fst x!} 
snd (P01 x) x₁ = {!   !} --{! x  !} , (λ x₁ → {!  snd (x x₁) !})  

-- P03 : {A : Set} {R : A  → Set} → ̸