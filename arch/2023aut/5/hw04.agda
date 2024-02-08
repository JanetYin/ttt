open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Lib.Equality
open import Lib.Bool
open import Lib.Sum hiding (comm⊎)
open import Lib.Sigma
open import Lib.Unit
open import Lib.Empty

-- Próbálkozz az iso1-gyel és az iso2-vel a gyakfájlból.

---------------------------------------------------

-- Írd meg az alábbi izomorfizmusokat.
-- Vigyázz, hogy ténylegesen bijekciók legyenek.

-- ezt kijavítottam; rossz volt
hw01 : (⊥ ⊎ ⊤) × (⊤ ⊎ ⊥) ↔ ⊤
hw01 = {!!}

hw02 : Bool × Bool ↔ ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤
hw02 = {!!}

hw03 : (Bool -> ⊤) ↔ ⊤
hw03 = {!!}

hw04 : (Bool -> ⊤) ↔ (⊤ -> ⊤)
hw04 = {!!}

hw05 : {A : Set} -> A × Bool ↔ A ⊎ A
hw05 = {!!}

hw06 : {A : Set} -> A × ⊥ ↔ ⊥ × ⊤
hw06 = {!!}

hw07 : {A : Set} -> (⊤ -> A) ↔ A
hw07 = {!!}

hw08 : {A : Set} -> (⊤ -> A) ↔ A × ⊤
hw08 = {!!}

hw09 : {A : Set} -> (A -> ⊥) ↔ ⊤
hw09 = {!!}

hw10 : {A : Set} -> A × A × A ↔ ((Bool ⊎ ⊤) -> A)
hw10 = {!!}

hw11 : {A B : Set} -> A × B ↔ ((⊤ -> A) × (⊤ -> B))
hw11 = {!!}

hw12 : {A B : Set} -> A × (A ⊎ B) ↔ B × A ⊎ A × A
hw12 = {!!}

hw13 : {A B C : Set} -> (A -> B -> (C -> A)) ↔ (A × B × C -> A)
hw13 = {!!}
