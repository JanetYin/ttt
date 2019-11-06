
-- mintaillesztés: ℕ, Bool, ⊎, ×, egyenlőség

open import lib

-- definiáld a következő függvényeket mintaillesztéssel:
--------------------------------------------------------------------------------

xor : Bool → Bool → Bool
xor = {!!}

Bool-eq : Bool → Bool → Bool
Bool-eq x y = {!!}

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
a + b = {!!}

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
a * b = {!!}

ℕ-eq : ℕ → ℕ → Bool
ℕ-eq n m = {!!}

lessThan : ℕ → ℕ → Bool
lessThan n m = {!!}

-- extra A típusparaméter
primrec' : (A : Set) → A → (ℕ → A → A) → ℕ → A
primrec' A z s n = {!!}

-- extra A típusparaméter
ifthenelse' : (A : Set) → Bool → A → A → A
ifthenelse' A b t f = {!!}

case' : (A B C : Set) → A ⊎ B → (A → C) → (B → C) → C
case' A B C ab f g = {!!}

-- ℕ-egyenlőségreláció
ℕEq : ℕ → ℕ → Set
ℕEq n m = {!!}
