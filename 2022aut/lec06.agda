{-# OPTIONS --guardedness #-}

module lec06 where

-- induktív típusok (+pozitivitás) & koinduktív típusok
--  esetleg: függő típusok intro

{-
induktív típus:

- konstruktorok felsorolása
- minden érték a konstruktorok véges sokszor
  való alkalmazása

-}

module Intro where

  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat

  -- konkrét számok: suc (suc (suc ... zero))

  -- rekurzió / indukció
  --   rekurzió: szeretnénk függvényt megadni
  --     egy induktív típusból

  add : Nat → (Nat → Nat)
  add zero    = λ m → m
  add (suc n) = λ m → suc (add n m)

  -- meg tudom ezt adni rekurzor vagy iterátor segítségével
  --   ha függvényt definiálok Nat-ból
  --     elég megadni a zero és suc eseteket
  --   emlékezzünk:
  --     ha bizonyítunk Nat-ról
  --       elég valnamit belátni zero-ról
  --            belátni, hogy suc megőrzi a tulajdonságot

  -- (rekurzió speciális esete az indukciónak)

-- szintaxisfák
------------------------------------------------------------

open import Data.Nat

-- egyszerű kifejezésnyelv

data NatExp : Set where
  lit : ℕ → NatExp
  add : NatExp → NatExp → NatExp
  mul : NatExp → NatExp → NatExp

-- data NatExp = Lit Nat | Add NatExp NatExp
--   | Mul NatExp NatExp

exp1 : NatExp      --  10 + (10 * 30)
exp1 = add (lit 10) (mul (lit 10) (lit 30))

-- interpeter
-- jelölés: ⟦_⟧  ("semantic bracket")

-- ⟦_⟧ : NatExp → ℕ
-- ⟦ lit n     ⟧ = n
-- ⟦ add e1 e2 ⟧ = ⟦ e1 ⟧ + ⟦ e2 ⟧
-- ⟦ mul e1 e2 ⟧ = ⟦ e1 ⟧ * ⟦ e2 ⟧

-- művelet: rekurzió mint általános művelet fákra
--   (Agda-ban van mintaillesztés
--    viszont formálisan erre úgy gondolunk mint egy
--    tömör jelölés a rekurzió elvére)

recNatExp :
    {A : Set}
  → (ℕ → A)      -- lit eset
  → (A → A → A)  -- add eset
  → (A → A → A)  -- mul eset
  → NatExp → A
recNatExp fl fa fm (lit n)     = fl n
recNatExp fl fa fm (add e1 e2) = fa (recNatExp fl fa fm e1)
                                    (recNatExp fl fa fm e2)
recNatExp fl fa fm (mul e1 e2) = fm (recNatExp fl fa fm e1)
                                    (recNatExp fl fa fm e2)

⟦_⟧ : NatExp → ℕ
⟦_⟧ = recNatExp (λ n → n) _+_ _*_


recNatExp' :
    {A : Set}
  → (ℕ → A)               -- lit eset
  → (NatExp → A → A → A)  -- add eset
  → (NatExp → A → A → A)  -- mul eset
  → NatExp → A
recNatExp' fl fa fm (lit n)     = fl n
recNatExp' fl fa fm (add e1 e2) = fa (add e1 e2)
                                     (recNatExp' fl fa fm e1)
                                     (recNatExp' fl fa fm e2)
recNatExp' fl fa fm (mul e1 e2) = fm (mul e1 e2)
                                     (recNatExp' fl fa fm e1)
                                     (recNatExp' fl fa fm e2)

-- opcionális házi feladat:
--   recNatExp' függvény definiálható
--   csak recNatExp  felhasználásával

-- pozitivitás
------------------------------------------------------------

-- megszorítás: induktív típus konstruktorai
--   "szigorú pozitívak"

-- ellenpélda:

{-# NO_POSITIVITY_CHECK #-}
data Fun : Set where
  fun : (Fun → Fun) → Fun

-- Haskell-ben:
--   data Fun = Fun (Fun -> Fun)

-- azt szeretnénk, hogy Fun ≃ (Fun → Fun)
--    (bijekció legyen Fun és Fun → Fun között)

-- emlékezzünk: nincs bijeckió A és (Bool → A) között

-- testszőleges lambda-kifejezéseket írhatunk

app : Fun → (Fun → Fun)
app (fun f) = f

lam1 : Fun
lam1 = fun (λ x → fun (λ y → x))

lam2 : Fun   -- típusozatlan lambda kalkulus beágyazása
lam2 = fun (λ f → fun (λ x → app f x))

-- végtelen ciklus

-- (λ x. x x) (λ x. x x)
--  = (λ x. x x)(λ x. x x)    -- egy lépés után

loop : Fun
loop = app (fun (λ x → app x x)) (fun (λ x → app x x))

-- szabály arra, hogy mit engedünk meg konstruktornak:
--    a típus amit definiálunk
--    nem lehet _→_ bal oldalán valamilyen konstruktor
--     mezőben

-- korábban definiált típus megjelenhet mezőben
-- függvény inputként!

data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : (ℕ → Tree A) → Tree A

-- végtelenül elágazó fa
--  minden node-nál meg kell adni megszámlálható sok
--    részfát

t1 : Tree ℕ
t1 = node (λ n → leaf n)
  -- n-edik részfa: leaf n

t2 : Tree ℕ
t2 = node (λ n → node (λ m → leaf (n + m)))

-- data Weird : Set where
--   weirdSuc : (ℕ → Weird) → Weird

-- data Weird : Set where
--   weirdSuc : Weird → Weird

-- data Empty : Set where

open import Data.Empty

{-# NO_POSITIVITY_CHECK #-}
data Explode : Set where
   explode : (Explode → ⊥) → Explode

-- bot : ⊥     -- logikai inkozisztencia:
-- bot = {!!}  --   ellentmondást be tudunk bizonyítani

exfalso : {A : Set} → ⊥ → A
exfalso ()

-- ha bot definiálható, akkor
--  minden lehetséges állítás bizonyítható
--  (nem szeretnénk, hogy minden bizonyítható legyen)

-- koinduktív típusok
------------------------------------------------------------

-- induktív vs. koinduktív
--  "ko" : dualitás

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

-- Haskell-ben:
--   data Stream a = Stream a (Stream a)

-- head :: Stream a -> a
-- head (Stream h tl) = h

-- tail :: Stream a -> Stream a
-- tail (Stream h tl) = tl

-- stream, ami 1-et ismétli
ones : Stream ℕ           -- ko-mintaillesztés
head ones = 1
tail ones = ones

open import Data.List hiding (head; tail)

takeS : {A : Set} → ℕ → Stream A → List A
takeS zero    s = []
takeS (suc n) s = head s ∷ takeS n (tail s)

-- különbség Haskell és Agda között:
--   Agda: minden függvény mindig teljes
--     még végtelen adatszerkezetekkel együtt is

-- Haskell: lista sum függvény

mapS : {A B : Set} → (A → B) → Stream A → Stream B
head (mapS f s) = f (head s)
tail (mapS f s) = mapS f (tail s)

open import Data.Bool

-- termination checking fail
-- filterS nem definiálható totálisan
-- filterS : {A : Set} → (A → Bool) → Stream A → Stream A
-- head (filterS f s) =
--   if f (head s) then head s else head (filterS f (tail s))
-- tail (filterS f s) =
--   if f (head s) then {!!} else {!!}

open import Data.Product

-- korekurzor Stream-re
corecStream :
  {A B : Set} → (B → A × B) → B → Stream A
head (corecStream step state) =
  proj₁ (step state)
tail (corecStream step state) =
  corecStream step (proj₂ (step state))

countFromZero : Stream ℕ
countFromZero = corecStream (λ n → n , suc n) 0

-- CoList
------------------------------------------------------------

open import Data.Maybe

record CoList (A : Set) : Set where
  coinductive
  field
    observe : Maybe (A × CoList A)
open CoList

goCountFromZero : ℕ → CoList ℕ
observe (goCountFromZero n) =
  just (n , goCountFromZero (suc n))

countFromZero' : CoList ℕ
countFromZero' = goCountFromZero 0

corecCoList :
   {A B : Set} → (B → Maybe (A × B)) → B → CoList A
observe (corecCoList step state) with step state
... | nothing      = nothing
... | just (a , b) = just (a , corecCoList step b)

countFromZero'' : CoList ℕ
countFromZero'' = corecCoList (λ n → just (n , suc n)) 0

-- corecCoList :
--    {A B : Set} → (B → Maybe (A × B)) → B → CoList A

-- emlékezzünk:
--   induktív listára mi a rekurzor:
--   nem más, mint foldr függvény

-- foldr : (A → B → B) → B → List A → B
--   át lehet írni a típust:

-- foldr     : (Maybe (A × B) → B) → List A → B
-- corecList : (B → Maybe (A × B)) → B → CoList A

--   lista duálisa a ko-lista
--

-- koindukció: megengedi a "produktív" végetelen
--   futást,
--   pl: szerver, ami végtelenül fut, viszont
--     mindig reszponzív



-- MAJD: szorzat tipust data-val megadni, mi a kulonbseg?
-- MAJD: nezzuk meg a tipusosztalyok implementaciojat Agdaban

-- kovetkezo ora egy perccel rovidebb
