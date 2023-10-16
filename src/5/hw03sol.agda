open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Lib.Equality
open import Lib.Bool
open import Lib.Sum hiding (comm⊎)
open import Lib.Sigma
open import Lib.Unit
open import Lib.Empty

-- Hány eleme van az alábbi típusoknak? Add meg az összeset (ha lehet).
a1 {-a2 a3 ...-} : Bool × Bool
a1 = {!!}
-- a2 = ?
-- a3 = ?
-- Itt persze annyit adj meg, ahány elem van.

-- Hasonlóan a későbbieknél is: számold ki, hány elem van, és add meg az összeset.
b1 : Bool ⊎ Bool
b1 = {!!}

c1 : ⊤ × ⊤
c1 = {!!}

d1 : ⊤ × (⊤ ⊎ ⊤)
d1 = {!!}

e1 : (⊤ × ⊤) ⊎ ⊤
e1 = {!!}

f1 : ⊥ ⊎ (⊤ ⊎ ⊥)
f1 = {!!}

g1 : (⊥ ⊎ ⊤) × ⊥
g1 = {!!}

h1 : (ℕ × ⊥) ⊎ ⊤
h1 = {!!}

i1 : Bool × Bool ⊎ Bool
i1 = {!!}

-----------------------------------------

-- Írd meg az alábbi izomorfizmusokat:

{-
false , false
false , true
true , false
true , true

inl tt
inr (inl tt)
inr (inr (inl tt))
inr (inr (inr tt))
-}

hiso1 : Bool × Bool ↔ ⊤ ⊎ (⊤ ⊎ (⊤ ⊎ ⊤))
fst hiso1 (false , false) = inl tt
fst hiso1 (false , true) = inr (inl tt)
fst hiso1 (true , false) = inr (inr (inl tt))
fst hiso1 (true , true) = inr (inr (inr tt))
snd hiso1 (inl tt) = false , false
snd hiso1 (inr (inl tt)) = false , true
snd hiso1 (inr (inr (inl tt))) = true , false
snd hiso1 (inr (inr (inr tt))) = true , true
-- Ehhez írok sok tesztesetet is, hogy lásd, ha a bijekció nem teljesül.
-- A későbbieknél már nem fogok; ott neked kell előtte logikusan kigondolni.
testhiso11 : fst hiso1 (false , false) ≡ fst hiso1 (false , true) -> ⊥
testhiso11 ()
testhiso12 : fst hiso1 (false , false) ≡ fst hiso1 (true , false) -> ⊥
testhiso12 ()
testhiso13 : fst hiso1 (false , false) ≡ fst hiso1 (true , true) -> ⊥
testhiso13 ()
testhiso14 : fst hiso1 (false , true) ≡ fst hiso1 (true , false) -> ⊥
testhiso14 ()
testhiso15 : fst hiso1 (false , true) ≡ fst hiso1 (true , true) -> ⊥
testhiso15 ()
testhiso16 : fst hiso1 (true , false) ≡ fst hiso1 (true , true) -> ⊥
testhiso16 ()
testhiso1inv : ∀ (bb : Bool × Bool) -> snd hiso1 (fst hiso1 bb) ≡ bb
testhiso1inv (false , false) = refl
testhiso1inv (false , true) = refl
testhiso1inv (true , false) = refl
testhiso1inv (true , true) = refl
-- Ez gyakorlatilag egy helyességbizonyítás is egyben.
-- Félév végére már fogjuk érteni.

