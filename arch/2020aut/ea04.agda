module lec.ea4 where

open import lib

{-
(λ f → f true) (λ x → true) = (f true)[f ↦ (λ x → true)] = (λ x → true) true = true[x↦true]=true
       ^ ^:Bool\__________/
       |        : Bool → Bool
    : Bool → Bool
\____________/
  : (Bool → Bool) → Bool      ≠ Bool → (Bool → Bool)



f : Bool → Bool    true : Bool
------------------------------
         f true : Bool

t : A → B          u : A
------------------------   → típus eliminációs szabálya
        t u : B


 (λ f → f false) (λ x → true) = (f false)[f ↦ (λ x → true)] = (λ x → true) false=true[x↦false] =
    true



(λ f → f true) (λ x → true) =  (λ f → f false) (λ x → true)



(λ f → f true) (λ x → true)
               \__________/
                : (C → Bool) = A
\____________/
 : (C → Bool) → B

-}

a = (λ f → f true) (λ x → true)

b : ℕ → Bool
b = (λ x → true)

c : {A : Set} → (Bool → A) → A
c = (λ f → f true)

d : {A : Set} → ((((A → ⊥) → ⊥) → A) → ⊥) → ⊥
d = λ f → f (λ nna → {!!})
-- ez egy túl bonyolult példa, de majd befejezzük

pred : ℕ → ℕ
pred = {!λ n → rec ? ? n!}

-- pred 0 = 0
-- pred 1 = 0
-- pred 2 = 1
-- pred 3 = 2
-- ...
{-
X       Bool       A→B          ℕ      A×B     ⊤      A⊎B        ⊥             A
-----------------------------------------------------------------------------------
Goal:X  true       λ x → ?      zero   ? , ?   tt     inj₁ ?                  ha van
(bev)   false                   suc ?                 inj₂ ?                  t : A feltétel,
                                                                              akkor t

—————   if t then  (t ?)        rec ?  proj₁ t        case t     exfalso t
t : X     ? else ?                ? t  proj₂ t          ? ?
(elim)
-}


e : {A : Set} → ((A ⊎ (A → ⊥)) → ⊥) → ⊥
e = λ w → w (inj₂ λ a → w (inj₁ a))

-- szerintem e segítségével megadható d

------------------------------------------------------------------------------------------

-- Most már van ⊥,⊤,⊎,×,→,ℕ. Nincs szükség Bool-ra. Bool := ⊤ ⊎ ⊤

Bool' = ⊤ ⊎ ⊤
true' : Bool'
true' = inj₁ tt  -- C-u C-u C-c C-,
false' : Bool'
false' = inj₂ tt
-- _+_ : ℕ → (ℕ → ℕ)
if'_then_else_ : {A : Set} → Bool' → A → A → A
if'_then_else_ = λ b → λ u → λ v → case b (λ x → u) (λ x → v)

-- szeretném: 
-- 1. if' true'  then 1 else 2 = 1
-- 2. if' false' then 1 else 2 = 2

--------------------------------------------------------------------

Ot = ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤ -- ⊤ ⊎ (⊤ ⊎ (⊤ ⊎ (⊤ ⊎ ⊤)))
o1 o2 o3 o4 o5 : Ot
o1 = inj₁ tt
o2 = inj₂ (inj₁ tt)
o3 = inj₂ (inj₂ (inj₁ tt))
o4 = inj₂ (inj₂ (inj₂ (inj₁ tt)))
o5 = inj₂ (inj₂ (inj₂ (inj₂ tt)))

{- forditas:
⊥          0
⊤          1
⊎          +
×          *
-}

Hat = (⊤ ⊎ ⊤) × (⊤ ⊎ ⊤ ⊎ ⊤) -- 2 * 3
-- h1 h2 h3 ... : Hat (HF)

Egy = ⊤ ⊎ ⊥  -- 1 + 0 = 1
e1 : Egy
e1 = inj₁ tt
-- e2 : Egy
-- e2 = inj₂ {!!} -- ilyen nincs

Nulla = (⊤ ⊎ ⊤ ⊎ ⊤) × ⊥   -- 3 * 0 = 0
hathaMegis : Nulla
hathaMegis = inj₁ tt , {!!}

Nulla' = ⊥
Nulla'' = ⊤ × ⊥
Nulla''' = ⊥ ⊎ ⊥

Egy' = ⊤
Egy'' = ⊤ × ⊤

-- A típusok így viselkednek, hogy van egy csomó egyelemű típus, csomó nulla elemű típus, etc.

-- Egy, Egy', Egy ≠ Egy'
Vegtelen = ℕ × ℕ

-- 0,1,+,*,^     → 
-- A → B      B^A  2^1 = 2

Ket = ⊤ → (⊤ ⊎ ⊤)
k1 k2 : Ket
k1 = λ x → inj₁ tt
k2 = λ x → inj₂ tt

Egy'''' = (⊤ ⊎ ⊤) → ⊤
e''' e'''' : Egy''''
e''' = λ x → case x (λ y → tt) (λ y → tt)
e'''' = λ x → tt
-- e''' = e'''' ⊤ tipus egyedisege miatt

-- 2^0 = 1
Egy5 = ⊥ → (⊤ ⊎ ⊤)
e5' : Egy5
e5' = {!!}
