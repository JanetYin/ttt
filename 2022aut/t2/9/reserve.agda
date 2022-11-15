open import lib

--------------------------------------------------------------------------------
--- Equality types
--------------------------------------------------------------------------------

EqBool : Bool → Bool → Set
EqBool true  true   = ⊤
EqBool false true   = ⊥
EqBool true  false  = ⊥
EqBool false false  = ⊤

-- Alternative:
-- data EqBool' : Bool → Bool → Set where
--   eq-true  : EqBool' true true
--   eq-false : EqBool' false false
-- + general equality types _≡_

-- Reflexivity
refl-Bool : {b : Bool} → EqBool b b
refl-Bool {b} = {!!}

-- Symmetry
sym-Bool : {x y : Bool} → EqBool x y → EqBool y x
sym-Bool {x} {y} = {!!}

-- Transitivity
trans-Bool : {x y z : Bool} → EqBool x y → EqBool y z → EqBool x z
trans-Bool {x} {y} {z} = {!!}

-- Transport: if x = y, then P x is equivalent to P y for any P : Bool → Set
-- Elements of P x can be "transported" to P y
transport-Bool : (P : Bool → Set) → (x y : Bool) → EqBool x y → P x → P y
transport-Bool = {!!}

not = λ b → if b then false else true

not-not : (b : Bool) → EqBool (not (not b)) b
not-not = {!!}

not-injective : (x y : Bool) → EqBool (not x) (not y) → EqBool x y
not-injective = {!!}

-- Boolean equality is decidable
dec-EqBool : (x y : Bool) → EqBool x y ⊎ (¬ EqBool x y)
dec-EqBool = {!!}

-- proof: f is either not, id, const true or const false.
f3 : (f : Bool → Bool) (b : Bool) → EqBool (f (f (f b))) (f b)
f3 f b = {!!}
  where
    f3-helper : (x y : Bool) → EqBool x (f true) → EqBool y (f false) → ∀ b → EqBool (f (f (f b))) (f b)
    f3-helper x y pt pf b = {!!}
