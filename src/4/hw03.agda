open import lib
open import Agda.Primitive

-- add meg az összes különböző elemét az alábbi típusoknak!
-- (nem feltétlen annyi lyuk van, amennyit megadtam)
-- segítség: A → B-nek |B|^|A| eleme van (miért?)

t1 t2 : ⊤ → Bool
t1 = {!!}
t2 = {!!}

t3 t4 : Bool → ⊤
t3 = {!!}
t4 = {!!}

t5 t6 : (Bool ⊎ ⊥) × (⊤ × ⊤)
t5 = {!!}
t6 = {!!}

t7 t8 : (Bool × (⊥ → Bool)) → (⊤ ⊎ ⊤)
t7 = {!!}
t8 = {!!}


-- add meg az alábbi típusok egy-egy elemét!
-- ügyelj arra, hogy az átalakítások közben az információkat is megőrizd
-- (tehát ténylegesen bijekció legyen)
idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = (λ {(inl a) → a ; (inr ()) }) , inl

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = {!!}

spec : {A B C : Set} → (A ⊎ B) ⊎ C ↔ C ⊎ (B ⊎ A)
spec = ?
