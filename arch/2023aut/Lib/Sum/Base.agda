{-# OPTIONS --safe #-}

module Lib.Sum.Base where

open import Lib.Sum.Type
open import Lib.Equality

case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
         (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (inl t) u v = u t
case (inr t) u v = v t

case-⊎ : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
         (t : A ⊎ B)(u : A → C)(v : B → C) → C
case-⊎ = case

elim-⊎ : ∀ {i j k}{A : Set i}{B : Set j}{C : A ⊎ B → Set k}
           (t : A ⊎ B)(u : (a : A) → C (inl a))(v : (b : B) → C (inr b)) → C t
elim-⊎ (inl t) u v = u t
elim-⊎ (inr t) u v = v t

ind-⊎ : ∀ {i j k}{A : Set i}{B : Set j}{C : A ⊎ B → Set k}
          (t : A ⊎ B)
          (u : {k : A ⊎ B}(a : A) → k ≡ inl a → C (inl a))
          (v : {k : A ⊎ B}(b : B) → k ≡ inr b → C (inr b)) → C t
ind-⊎ (inl t) u v = u t refl
ind-⊎ (inr t) u v = v t refl

fromInl : ∀{i j}{A : Set i}{B : Set j} → (B → A) → A ⊎ B → A
fromInl f t = case t (λ x → x) f

fromInr : ∀{i j}{A : Set i}{B : Set j} → (A → B) → A ⊎ B → B
fromInr f t = case t f (λ x → x)

reduce : ∀{i}{A : Set i} → A ⊎ A → A
reduce t = case t (λ x → x) (λ x → x)

swap : ∀{i j}{A : Set i}{B : Set j} → A ⊎ B → B ⊎ A
swap (inl x) = inr x
swap (inr x) = inl x

map : ∀{i j k l}{A : Set i}{B : Set j}{C : Set k}{D : Set l} →
       (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
map f g t = case t (λ x → inl (f x)) (λ x → inr (g x))