module gy09 where

open import Lib

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

-- ∀a(P(a) ∧ Q(a)) <-> ∀aP(a) ∧ ∀aQ(a)
∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = λ _ _ _ → (λ f → (λ a → fst (f a)) , (λ a → snd (f a)))
                   , λ where (p , q) a → p a , q a

∀⊎-distr : (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr = λ _ _ _ → λ f a → case f (λ p → inl (p a)) (λ q → inr (q a))

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = λ f → case (f Bool P Q g) (λ p → p true) (λ q → q false) where
  P : Bool → Set
  P false = ⊤
  P true = ⊥

  Q : Bool → Set
  Q false = ⊥
  Q true = ⊤

  g : (a : Bool) → P a ⊎ Q a
  g false = inl tt
  g true = inr tt

Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr = λ _ _ _ → λ where (a , pa , qa) → (a , pa) , (a , qa)

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' = λ f → p (f Bool P Q ((false , tt) , (true , tt))) where
  P : Bool → Set
  P false = ⊤
  P true = ⊥

  Q : Bool → Set
  Q false = ⊥
  Q true = ⊤

  p : Σ Bool (λ a → Σ (P a) (λ _ → Q a)) → ⊥
  p (false , ())
  p (true , ())

Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}

¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ = {!!}

¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ = {!!}

¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}

Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}

AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!!}

∀∀ : Dec ((A B : Set)(R : A → B → Set) → (∀ a → ∀ b → R a b) → (∀ b → ∀ a → R a b))
∀∀ = inl λ _ _ _ → λ r b a → r a b

→∀ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → ((∀ x → P x) → (∀ x → Q x)) → ∀ x → P x → Q x)
→∀ = inr λ f → f Bool P Q (λ p b → p false) true tt where
  P : Bool → Set
  P true = ⊤
  P false = ⊥

  Q : Bool → Set
  Q _ = ⊥