module tut4 where
open import lib

-- Emacs key bindings (C = Ctrl, M = Alt):
-- C-x C-f : create or open a file
-- C-x C-s : save a file
-- C-x C-c : close Emacs
-- M-w : Copy
-- C-y : Paste
--
-- Agda-mode key bindings:
-- C-c C-l : Typecheck
-- C-c C-n : Evaluate
-- C-c C-, : Check the type of a hole
-- C-c C-. : Check the type of a hole, and the type of the expresion in the hole
-- C-c C-SPACE : Fill a hole
-- C-c C-r : Try to automatically fill a hole
--
-- Symbols: λ = \lambda
--          × = \times
--          → = \r
--          ₁ = \_1
--          ₂ = \_2
--          ⊎ = \u+
--          ≤ = \le
--          ↔ = \<->
--          ⊤ = \top
--          ⊥ = \bot
--          ¬ = \neg

--------------------------------------------------------------------------------
-- Coproducts
--------------------------------------------------------------------------------

-- Rules for coproducts:
--   inj₁ : A → A ⊎ B
--   inj₂ : B → A ⊎ B
--   case : A ⊎ B → (A → C) → (B → C) → C

a1 : Bool ⊎ Bool
a1 = inj₁ true

a2 : Bool ⊎ Bool
a2 = inj₂ false

f1 : Bool ⊎ Bool → Bool
f1 = λ b → case b (λ x → x) λ x → if x then false else x


bool↔⊎-l : Bool → ⊤ ⊎ ⊤
bool↔⊎-l = λ b → if b then inj₁ tt else inj₂ tt

bool↔⊎-r : ⊤ ⊎ ⊤ → Bool
bool↔⊎-r = λ x → case x (λ _ → true) (λ _ → false)

bool↔⊎ : Bool ↔ ⊤ ⊎ ⊤
bool↔⊎ = bool↔⊎-l , bool↔⊎-r

-- Define assoc⊎ to prove that coproducts are associative
--   A ↔ B  is the same as  (A → B) × (B → A)

assoc⊎-l : (X ⊎ Y) ⊎ Z → X ⊎ (Y ⊎ Z)
assoc⊎-l = λ p → case p (λ q → case q (λ x → inj₁ x) λ y → inj₂ (inj₁ y)) (λ z → inj₂ (inj₂ z))

assoc⊎-r : X ⊎ (Y ⊎ Z) → (X ⊎ Y) ⊎ Z
assoc⊎-r = λ p → case p (λ x → inj₁ (inj₁ x)) (λ q → case q (λ y → inj₁ (inj₂ y)) (λ z → inj₂ z))

assoc⊎ : (X ⊎ Y) ⊎ Z ↔ X ⊎ (Y ⊎ Z)
assoc⊎ = assoc⊎-l , assoc⊎-r

-- Is (λ x → assoc⊎-l (assoc⊎-r x)) the same as (λ x → x) ?

-- Same questions for the following logical equivalences

assoc× : (X × Y) × Z ↔ X × (Y × Z)
assoc× = (λ p → ( proj₁ (proj₁ p) , (proj₂ (proj₁ p) , proj₂ p) )) , (λ p → ((proj₁ p , proj₁ (proj₂ p)) , proj₂ (proj₂ p)))

cocurry : (X ⊎ Y → Z) ↔ (X → Z) × (Y → Z)
cocurry = (λ f → (λ x → f (inj₁ x)) , (λ y → f (inj₂ y))) , λ f xy → case xy (proj₁ f) (proj₂ f)

-- equiv0 : X ↔ X × X
-- equiv0 = {!!}

-- Bonus: define div2 : ℕ → ℕ ⊎ ℕ such that
--   if n is even, then div2 n = inj₁ (n / 2)
--   if n is odd, then div2 n = inj₂ ((n-1) / 2)
div2 : ℕ → ℕ ⊎ ℕ
div2 = λ n → primrec (inj₁ 0) (λ _ x → case x (λ a → inj₂ a) (λ a → inj₁ (suc a))) n

--------------------------------------------------------------------------------
-- Negation and the empty type
--------------------------------------------------------------------------------

-- The empty type ⊥ has one elimination rule:
--   exfalso : ⊥ → A        for any type A

-- ¬ X  is the same as  X → ⊥

neg× : ¬ X → ¬ (X × Y)
neg× = {!!}

neg⊎ : ¬ (X ⊎ Y) → ¬ X
neg⊎ = {!!}

f2 : ¬ (X × ¬ X)
f2 = {!!}

return¬ : X → ¬ ¬ X
return¬ = {!!}

f3 : ¬ ¬ ¬ X → ¬ X
f3 = {!!}
