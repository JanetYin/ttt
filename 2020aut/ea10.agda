module lec.ea10 where

open import lib

Eqb : Bool → Bool → Set
Eqb x y = if x then (if y then ⊤ else ⊥) else (if y then ⊥ else ⊤) 
reflb : {b : Bool} → Eqb b b
reflb {b} = indBool (λ b → Eqb b b) tt tt b

not = λ x → if x then false else true

module Second1 where
  and : Bool → Bool → Bool
  and x y with not y
  ... | true  = false
  ... | false = x

module Second2 where
  f : Bool → Bool → Bool
  f true  x = false
  f false x = x

  and : Bool → Bool → Bool
  and x y = f (not y) x

  andProp' : (t : Bool) → Eq Bool (and true t) t
  andProp' t = indBool (λ t → Eq Bool (and true t) t) refl refl t

  andProp : (t : Bool) → Eq Bool (and t true) t
  andProp t = refl

module First where
  and : Bool → Bool → Bool
  and true  y = y
  and false y = false
  -- and = λ x y → if x then y else false

  andProp' : (t : Bool) → Eqb (and true t) t
  andProp' = λ t → reflb {t}

  andProp : (t : Bool) → Eqb (and t true) t
  andProp = indBool (λ t → Eqb (and t true) t) tt tt

-- and = λ x y → if not y then false else x

module Third where
  and : Bool → Bool → Bool
  and true  true  = true
  and true  false = false
  and false true  = false
  and false false = false

  andProp' : (t : Bool) → Eq Bool (and true t) t
  andProp' = λ t → indBool (λ t → Eq Bool (and true t) t) refl refl t

  -- and = λ x y → if x
  --   then
  --     (if y then true else false)
  --   else
  --     (if y then false else false)
{-
mintaillesztés: egyenlőségekkel adom meg a függvényeket, és 
  ezek és csak ezek a definíció szerinti egyenlőségek igazak a függvényre
  nehézkes (with-re van szükség vagy segédfüggyényre) mintát illeszteni nem a
    bemenetre
eliminátor: könnyű bármire mintát illeszteni; az Agda nem írja ki, hogy milyen
  definíció szerinti egyenlőségek igazak; (maguk a függények is egyenlők lesznek); könnyebb kezelni elméletileg
-}
f : Bool → Bool
f true = false
f false = false
g : Bool → Bool
g true = false
g false = false

f' : Bool → Bool
f' = λ x → if x then false else false
g' : Bool → Bool
g' = λ x → if x then false else false

fg : Eq (Bool → Bool) f g
fg = {!!} -- ezt Agdában nem lehet bebizonyítani...

fg' : Eq (Bool → Bool) f' g'
fg' = refl

-- without-K

-- no-pattern-matching

-- az Agda inkonzisztens, ha a következő lyuk betölthető:
bottom : ⊥
bottom = {!!}

-- Az Agda működéséről tanultunk: szabályok, amik szerint az Agda
-- működik.  szabályok: típusonként. minden típushoz: típuslétrehozó,
-- bevezető, elim, számítási, egyediség; minden típushoz egyszerű és
-- függő szabályok, a függő általánosabb. Konkrétan: →,Σ,⊎,⊥,⊤,Bool,ℕ,Set,Eq

-- intuíció:
--   logika, → implikáció "minden", Σ és "létezik", ⊎ vagy, ⊥ hamis, ⊤ igaz,
--           Eq egyenlőség, ¬ A = A → ⊥
--   halmazok: → függvénytér exponenciális, × Descartes szorzat, ⊎ diszjunkt
--             unió, ⊥ üres halmaz, ⊤ egyelemű halmaz, Bool kételemű halmaz,
--             ℕ természetes számok halmaza
--             (A ⊎ B) × C ↔ (A × C) ⊎ (B × C)
--   Bool és ℕ algebrai tulajdonságai (test, kommutatív félgyűrű)
--   - a tulajdonságok használata, pl. ∀ x y. (x+y)² = x² + 2xy + y²

_+_ : ℕ → ℕ → ℕ
zero  + b = b
suc a + b = suc (a + b)

idl : (a : ℕ) → Eq ℕ (zero + a) a
idl = λ a → refl

cong : {A B : Set}(f : A → B){a a' : A} → Eq A a a' → Eq B (f a) (f a')
cong f refl = refl

idr : (a : ℕ) → Eq ℕ (a + zero) a
idr = λ a → indℕ (λ a → Eq ℕ (a + 0) a)
  refl
  (λ n e → cong suc e)
  a

-- Eqℕ az (Eq ℕ) helyett

-- kell nehany koztes lepes

comm : (a b : ℕ) → Eq ℕ (a + b) (b + a)
comm = {!!}
