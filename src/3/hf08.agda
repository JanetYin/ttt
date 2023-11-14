module hf08 where

open import Lib

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = {!!}

f11 : Dec ((P Q : Set) → (P → Q) × Q → P)
f11 = {!   !}

f12 : Dec ((A B : Set) → (A → B) → ¬ ¬ A → ¬ ¬ B)
f12 = {!   !}

f13 : Dec ((P Q : Set) → (P → Q) → ¬ ¬ (¬ P ⊎ Q))
f13 = {!   !}

f14 : Dec ((P Q : Set) → (P ↔ Q) → (¬ P × Q) ⊎ (P × ¬ Q))
f14 = {!   !}

f15 : Dec ((P Q R S : Set) → (P → Q) × (R → S) × (¬ P ⊎ S) → (Q ⊎ ¬ R))
f15 = {!   !}

-- Ez már megvolt a gyakorlaton!
f16 : Dec ((P Q : Set) → P × Q ↔ ((P → Q) ↔ P))
f16 = {!   !}

f17 : Dec ((P Q : Set) → (P → Q) ↔ ((P ⊎ ¬ Q) ↔ Q))
f17 = {!   !}

f18 : Dec ((P Q : Set) → (¬ P ⊎ Q) ↔ P → P × ¬ Q)
f18 = {!   !}

-- Sokat kell ezzel szőrőzni. Amolyan igazi bizonyítás!
-- Minden adja magát, csak sokáig adja magát.
f19 : {X Y : Set} → Dec (¬ ((X ↔ Y) ↔ (¬ X ↔ ¬ Y)))
f19 = {!   !}

----------------------------------------------
-- Elsőrendű formalizálás saját univerzumon --
----------------------------------------------

module Universe
  (Élőlény : Set)
  (Rovar : Élőlény → Set)
  (Bogár : Élőlény → Set)
  (Kitines : Élőlény → Set)
  (Szarvasbogár : Élőlény → Set)
  (legjobbBarát : Élőlény → Élőlény)
  (Szarvas : Élőlény)
  (_===_ : Élőlény → Élőlény → Set)
  where

  -- Minden bogár rovar, de nem minden rovar bogár.
  Állítás1 : Set
  Állítás1 = {!   !}

  -- Szarvasnak, a szarvasbogárnak kitines a szárnyfedője.
  Állítás2 : Set
  Állítás2 = {!   !}

  -- Egy rovarnak nincs kitines szárnyfedője vagy bogár.
  Állítás3 : Set
  Állítás3 = {!   !}

  -- Szarvas legjobb barátja bogár.
  Állítás4 : Set
  Állítás4 = {!   !}

  -- Van olyan rovar, akinek a legjobb barátja szarvasbogár.
  Állítás5 : Set
  Állítás5 = {!   !}


  -- Van két olyan bogár, akik a legjobb barátai egymásnak.
  Állítás6 : Set
  Állítás6 = {!   !}