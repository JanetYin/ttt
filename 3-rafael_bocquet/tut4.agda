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
a1 = inj₁ {!!}

a2 : Bool ⊎ Bool
a2 = inj₂ {!!}

f1 : Bool ⊎ Bool → Bool
f1 = λ b → case b {!!} {!!}


bool↔⊎-l : Bool → ⊤ ⊎ ⊤
bool↔⊎-l = {!!}

bool↔⊎-r : ⊤ ⊎ ⊤ → Bool
bool↔⊎-r = {!!}

bool↔⊎ : Bool ↔ ⊤ ⊎ ⊤
bool↔⊎ = {!!}

-- Define assoc⊎ to prove that coproducts are associative
--   A ↔ B  is the same as  (A → B) × (B → A)

assoc⊎-l : (X ⊎ Y) ⊎ Z → X ⊎ (Y ⊎ Z)
assoc⊎-l = {!!}

assoc⊎-r : X ⊎ (Y ⊎ Z) → (X ⊎ Y) ⊎ Z
assoc⊎-r = {!!}

assoc⊎ : (X ⊎ Y) ⊎ Z ↔ X ⊎ (Y ⊎ Z)
assoc⊎ = {!!}

-- Is (λ x → assoc⊎-l (assoc⊎-r x)) the same as (λ x → x) ?

-- Same questions for the following logical equivalences

assoc× : (X × Y) × Z ↔ X × (Y × Z)
assoc× = {!!}

cocurry : (X ⊎ Y → Z) ↔ (X → Z) × (Y → Z)
cocurry = {!!}

equiv0 : X ↔ X × X
equiv0 = {!!}

-- Bonus: define div2 : ℕ → ℕ ⊎ ℕ such that
--   if n is even, then div2 n = inj₁ (n / 2)
--   if n is odd, then div2 n = inj₂ ((n-1) / 2)
div2 : ℕ → ℕ ⊎ ℕ
div2 = {!!}

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
