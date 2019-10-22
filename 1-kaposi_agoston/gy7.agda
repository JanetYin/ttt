module gy7 where

open import lib

⊎→dist : ((X ⊎ Y) → Z) ↔ (X → Z) × (Y → Z)
⊎→dist = {!!}

anything' : ¬ ¬ X → ¬ X → Y
anything' = {!!}

¬¬¬¬return : X → ¬ ¬ ¬ ¬ X
¬¬¬¬return = {!!}

¬¬join' : ¬ ¬ ¬ X → ¬ X
¬¬join' = {!!}

function¬ : (X → Y) → ¬ Y → ¬ X
function¬ = {!!}

function¬' : (X → Y) × ¬ Y → ¬ X
function¬' = {!!}

-- de Morgan
¬× : ¬ (X × Y) ← ¬ X ⊎ ¬ Y
¬× = {!!}

build→ : ¬ X ⊎ Y → (X → Y)
build→ = {!!}

¬¬invol : ¬ ¬ ¬ X ↔ ¬ X
¬¬invol = {!!}

nocontra : ¬ (X ↔ ¬ X)
nocontra = {!!}

¬¬dnp : ¬ ¬ (¬ ¬ X → X)
¬¬dnp = {!!}

¬¬lem : (A : Set) → ¬ ¬ (A ⊎ ¬ A)
¬¬lem = {!!}


eqs3¬1¬ : ¬ ¬ ¬ X ↔ ¬ X
eqs3¬1¬ = {!!}

eqs4¬2¬ : ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
eqs4¬2¬ = {!!}

---------------------------------------------------------
-- Universe
---------------------------------------------------------

_^3 : Set → Set
A ^3 = {!!}

_*'_ : Set → ℕ → Set
_*'_ = {!!}

_^'_ : Set → ℕ → Set
_^'_ = {!!}

-- finite set with n number of elements
Fin : ℕ → Set
Fin = {!!}

f0 f1 f2 : Fin 3
f0 = {!!}
f1 = {!!}
f2 = {!!}

sucF3 : Fin 3 → Fin 3
sucF3 = {!!}

mod3 : ℕ → Fin 3
mod3 = {!!}

F0 F1 F2 F3 F4 : Fin 5
F0 = {!!}
F1 = {!!}
F2 = {!!}
F3 = {!!}
F4 = {!!}

tff : Bool ^' 3
tff = {!!} -- true , (false , (false , tt))

ftft : Bool ^' 4
ftft = {!!}

Eqb : Bool → Bool → Set
Eqb = λ x y → if x then (if y then ⊤ else ⊥) else (if y then ⊥ else ⊤)

true=true : Eqb true true
true=true = {!!}

true=false : Eqb true false
true=false = {!!}


---------------------------------------------------------
-- Dependent function space
---------------------------------------------------------

ID : (A : Set) → A → A
ID = {!!}

CONST : (A B : Set) → A → B → A
CONST = {!!}

comm× : (A B : Set) → (A × B) ↔ (B × A)
comm× = {!!}

-- Szorgalmi:
sucFn : (n : ℕ) → Fin n → Fin n
sucFn = {!!}

-- Szorgalmi:
modFn : (n : ℕ) → ℕ → Fin n
modFn = {!!}

---------------------------------------------------------
-- First order logic
---------------------------------------------------------

module firstOrder
  (A : Set)
  (P Q : A → Set)
  where

  ∀× : ((x : A) → P x × Q x) ↔ ((x : A) → P x) × ((x : A) → Q x)
  ∀× = {!!}

  ∀⊎ : ((x : A) → P x ⊎ Q x) ← ((x : A) → P x) ⊎ ((x : A) → Q x)
  ∀⊎ = {!!}

  ¬¬∀ : ¬ ¬ ((x : A) → P x) → (x : A) → ¬ ¬ (P x)
  ¬¬∀ = {!!}

-- Define toSet function which is ⊤ if true and ⊥ if false
toSet : Bool → Set
toSet = {!!}

