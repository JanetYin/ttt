{-# OPTIONS --guardedness #-}

module ea04 where

open import lib hiding (ℕ; zero; suc; Bool; true; false; if_then_else_; _+_)

-- kviz

{-
(λ x → case x (λ y → true) (λ z → true)) = (λ x → true)

(λ x → if x then true else true) =? (λ x → true)

(λ _ → true) = (λ _ → true) ?

Bool egyediseg szabalya:

          x:Bool ⊢ t : A
---------------------------------------   ebbol kovetkezik, hogy  (λ x → true) = (λ x → if x then true[x↦true] else true[x↦false])
t = if x then t[x↦true] else t[x↦false]

exfalso : {A : Set} → ⊥ → A

(λ x → exfalso x) =? 4

α: (λ x → t) = (λ y → t[x↦y])
β: (λ x → t) u = t[x↦u]
η: f = (λ x → f x)


-}

module T where
  open import lib

  f : ℕ → ℕ
  f = λ x → x + 1

  f1 : ⊥ → ℕ
  f1 = exfalso

  f2 : ⊥ → (ℕ ⊎ ⊥)
  f2 = exfalso

-- ez az eloadas 8 perccel rovidebb

-- definicio szerinti egyenlosegek, η szabalyok, curry, uncurry korbemegy

curry : {A B C : Set} → (A × B → C) → (A → B → C)
curry = λ f a b → f (a , b)

uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
uncurry = λ f ab → (f (fst ab)) (snd ab)

-- (A → B → C) ≅ (A × B → C) izomorf tipusok
{-
surjective pairing, η szorzat tipusra:

t : A × B
-------------------
t = (fst t , snd t)


uncurry (curry f) =(def. + β)
uncurry (λ a b → f (a , b)) =(def.)
(λ f → λ ab → (f (fst ab)) (snd ab)) (λ a b → f (a , b)) =(β)
(λ ab → (f (fst ab)) (snd ab))[f ↦ (λ a b → f (a , b))] =
λ ab → ((λ a b → f (a , b)) (fst ab)) (snd ab) =(β)
λ ab → ((λ b → f (a , b))[a → fst ab]) (snd ab) =
λ ab → (λ b → f (fst ab , b)) (snd ab) =(β)
λ ab → f (fst ab , snd ab) =(surj.pairing,η for ×)
λ ab → f ab =(η)
f

osszefoglalas az Agda-beli egyenlosegekrol (operacios szemantika, Agda programok vegrehajtasa)

α: (λ x → f x) = (λ y → f y)   "kotott valtozo neve nem szamit"
β: (λ x → t) u = t[x↦u]

    f : A → B
   -------------η fuggvenyre
   f = λ x → f x

definiciok, mintaillesztesek (pl. if true then x else y = x, plus = λ x y → x + y)

η szorzat tipusra:

   t : A × B
   -------------------
   t = (fst t , snd t)

η egyelemu tipusra:

   t : ⊤
   ------
   t = tt

HF:

curry (uncurry f) =
... =
=
f

(A → B → C) ≅ (A × B → C)   IGAZ
⊤ ⊎ ⊥       ≇ ⊤             SAJNOS NEM


-}

g : ⊤ ⊎ ⊥ → ⊤    -- 1^(1+0) = 1^1 = 1
g = _
{-
g =(η)
(λ x → f x) =(η ⊤ tipusra)
(λ x → tt)
-}

g⁻¹ : ⊤ → ⊤ ⊎ ⊥
g⁻¹ x = inl x
{-
               x : ⊤
----------------------------------
g (g⁻¹ x) =(η ⊤-ra) tt =(η ⊤-ra) x

g⁻¹ (g x) =(η ⊤-ra) g⁻¹ tt =(def.) inl tt ≠ x
-}

{-
finite type isos:

A ⊎ B ↔ B ⊎ A   kommutativitas
A × B ≅ B × A

A tipusok a ⊎,⊥,×,⊤-al kommutativ felgyurut alkotnak, van exponencialis is, (high school algebra)
-}

-- induktiv tipus = data-val van megadva, eddig volt ⊥, ⊎, Bool, ℕ
{-
data Bool : Set where
  true false : Bool

data Egtaj : Set where
  E K D Ny : Egtaj

0 = zero, 1 = suc zero, 2 = suc (suc zero), 3 = suc (suc (suc zero)), ...
-}
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

Bool = ⊤ ⊎ ⊤
true false : Bool
true = inl tt
false = inr tt
if_then_else_ : {A : Set} → Bool → A → A → A
if_then_else_  = λ b t f → case b (λ _ → t) (λ _ → f)

-- Maybe A = A ⊎ ⊤
data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just    : A → Maybe A

pred : ℕ → Maybe ℕ
pred zero    = Nothing
pred (suc n) = Just n

zerosuc : Maybe ℕ → ℕ
zerosuc Nothing  = zero
zerosuc (Just n) = suc n

-- HF: pred es zerosuc "inverzek"

-- Nat, Maybe, pred, zerosuc, rekurzio(double,_+_,_*_,ack), iterator, rekurzor

_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

-- iterator, fold, catamorphism, nondependent eliminator
iteℕ : {A : Set} → A → (A → A) → ℕ → A
iteℕ a f zero = a
iteℕ a f (suc n) = f (iteℕ a f n)
-- suc (suc (suc zero)) ⊢> f (f (f a))

_+'_ : ℕ → ℕ → ℕ
_+'_ = λ a b → iteℕ b suc a

-- iteℕ-el nem lehet megadni a pred-et ugy, hogy pred (suc n) = n, de
-- ugy meg lehet adni hogy pred (suc zero) = zero, es pred (suc (suc
-- zero)) = suc zero, es predd (suc (suc (suc zero))) = suc (suc
-- zero), stb.

-- recursor:
recℕ : {A : Set} → A → (ℕ → A → A) → ℕ → A
recℕ a f zero = a
recℕ a f (suc n) = f n (recℕ a f n)

-- List(length,sum,map,ite,rec), Expr(eval), RoseTree(countNodes)

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

-- kategoriaelmelet, category theory

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public

coit : {A B : Set} → (B → A) → (B → B) → B → Stream A
head (coit h t b) = h b
tail (coit h t b) = coit h t (t b)

-- kovetkezo eloadas 10 perccel rovidebb
