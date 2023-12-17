module hf13 where

open import Lib hiding (_≟⊤_ ; _≟⊥_)

-----------------------------
-- Eldönthetőség
-----------------------------

_≟⊤_ : (a b : ⊤) → Dec (a ≡ b)
_≟⊤_ = ?

_≟⊥_ : (a b : ⊥) → Dec (a ≡ b)
_≟⊥_ = ?

postulate
  funext : ∀{i j}{A : Set i}{B : Set j}{f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
  -- Ez MLTT-ben nem bizonyítható, de kubikális agdában igen.

happly : ∀{i j}{A : Set i}{B : Set j}{f g : A → B} → f ≡ g → (∀ x → f x ≡ g x)
happly = ?

-- funext és happly szükségesek!
-- Segítség: Érdemes definiálni egy segédfüggvényt, amely a négy lehetséges függvényt felismeri,
--           mindegyik ágon megkapva az adott ágon lévő igaz egyenlőséget.
_≟Bool→Bool_ : (b b' : Bool → Bool) → Dec (b ≡ b')
b ≟Bool→Bool b' = ?