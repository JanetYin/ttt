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

{-
(inr tt , inl tt)

tt
-}

hw01 : (⊥ ⊎ ⊤) × (⊤ ⊎ ⊥) ↔ ⊤
fst hw01 (inr tt , inl tt) = tt
snd hw01 tt = inr tt , inl tt

hw02 : Bool × Bool ↔ ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤
hw02 = {!!}

{-
λ {true -> tt; false -> tt}

tt
-}

hw03 : (Bool -> ⊤) ↔ ⊤
fst hw03 f = tt
snd hw03 tt = λ {true -> tt; false -> tt}

{-
λ {false -> false; true -> false}
λ {false -> false; true -> true}
λ {false -> true;  true -> false}
λ {false -> true;  true -> true}

false , false
false , true
true  , false
true  , true
-}
hw035 : (Bool -> Bool) ↔ Bool × Bool
-- fst hw035 f = if f false then (if f true then true , true else true , false)
--                          else (if f true then false , true else false , false)
fst hw035 f = f false , f true
snd hw035 (false , false) = λ {false -> false; true -> false}
snd hw035 (false , true) = {!!}
snd hw035 (true , snd₁) = {!!}

hw04 : (Bool -> ⊤) ↔ (⊤ -> ⊤)
hw04 = {!!}

{-
tfh. A = {a1, a2, a3}
igazából _akármilyen_ A-ra működnie kell;
de érdemes kísérletezni egy konkrét A halmazzal

a1 , false
a1 , true
a2 , false
a2 , true
a3 , false
a3 , true

inl a1
inr a1
inl a2
inr a2
inl a3
inr a3

ötlet: az első elem, ami be van csomagolva
       és false, ha inl; true, ha inr
-}

hw05 : {A : Set} -> A × Bool ↔ A ⊎ A
fst hw05 (a , false) = inl a
fst hw05 (a , true) = inr a
snd hw05 (inl a) = a , false
snd hw05 (inr a) = a , true

hw06 : {A : Set} -> A × ⊥ ↔ ⊥ × ⊤
hw06 = {!!}

hw07 : {A : Set} -> (⊤ -> A) ↔ A
hw07 = {!!}

hw08 : {A : Set} -> (⊤ -> A) ↔ A × ⊤
hw08 = {!!}

hw09 : {A : Set} -> (⊥ -> A) ↔ ⊤
fst hw09 f = tt
snd hw09 tt = λ {()}

{-
tfh. A = {a1; a2}

A × A × A
a1 , a1 , a1
a1 , a1 , a2
a1 , a2 , a1
a1 , a2 , a2
a2 , a1 , a1
...
a2 , a2 , a2

λ {(inl false) -> a1; (inl true) -> a1; (inr tt) -> a1}
λ {(inl false) -> a1; (inl true) -> a1; (inr tt) -> a2}
...
λ {(inl false) -> a2; (inl true) -> a2; (inr tt) -> a2}
-}

{-
tfh. A = {a1; a2}
λ {tt -> inl a1}
λ {tt -> inl a2}
λ {tt -> inr a1}
λ {tt -> inr a2}

inl a1
inl a2
inr a1
inr a2
-}

hw095 : {A : Set} -> (⊤ -> A ⊎ A) ↔ A ⊎ A
fst hw095 f = f tt
snd hw095 ava = λ {tt -> ava}

{-
tfh. A = {a1, a2}

A × A × A
a1 , a1 , a1
a1 , a1 , a2
a1 , a2 , a1
...
a2 , a2 , a2

λ {(inl false) -> a1; (inl true) -> a1; (inr tt) -> a1}
λ {(inl false) -> a1; (inl true) -> a1; (inr tt) -> a2}
λ {(inl false) -> a1; (inl true) -> a2; (inr tt) -> a1}
λ {(inl false) -> a1; (inl true) -> a2; (inr tt) -> a2}
...
λ {(inl false) -> a2; (inl true) -> a2; (inr tt) -> a2}

-}

hw10 : {A : Set} -> A × A × A ↔ ((Bool ⊎ ⊤) -> A)
fst hw10 (x , y , z) = λ {(inl false) -> x; (inl true) -> y; (inr tt) -> z}
snd hw10 f = f (inl false) , f (inl true) , f (inr tt)

hw11 : {A B : Set} -> A × B ↔ ((⊤ -> A) × (⊤ -> B))
hw11 = {!!}

hw12 : {A B : Set} -> A × (A ⊎ B) ↔ B × A ⊎ A × A
hw12 = {!!}

hw13 : {A B C : Set} -> (A -> B -> (C -> A)) ↔ (A × B × C -> A)
hw13 = {!!}
