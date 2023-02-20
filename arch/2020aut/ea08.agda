module lec.ea8 where
open import lib
{-
t : (x : Bool) → if x then ℕ else Bool
t true  : ℕ
t false : Bool

t : Bool → Set
t = λ x → if x then ℕ else Bool
t true  = ℕ
t false = Bool

hasonlóság (λ x → t) és ((x : Bool) → t) között:
  mindegyikben t-ben kötött változó az x
különbégek:
  (λ x → t)        : A → B
  ((x : Bool) → t) : Set

függő függvény típust szokás Π-nek is nevezni
gyakori hiba a λ és a Π összekeverése

------------------------------------------------------

típusok: →, Bool, ℕ, ×, ⊎, ⊥, ⊤
         Set, implicit paraméterek
         
         VecBool : ℕ → Set
         VecBool = λ n → rec ⊤ (λ X → X × Bool) n
         VecBool 3 = ((⊤ × Bool) × Bool) × Bool

         → függő változata:
         (A : Set) → A → A
         Set       → ? → ?
         (x : Bool) → if x then ℕ else Bool
         
MOST: megnézzük a Bool, ℕ, ×, ⊎, ⊥, ⊤ függő változatát
a nem-függő változok elfelejthetők

MIRE JÓ? konkrét példa:
f : (x : Bool) → if x then ℕ else Bool
f = λ x → t

A : Set, B : A → Set           A:=Bool, B:=λ x → if x then ℕ else Bool
--------------------tipusbev   ---------------------------------------
 (x : A) → B x : Set           (x:A)→B x = (x : Bool) → if x then ℕ else Bool

t : B x, feltéve, hogy x : A      t : (x : A) → B x      u : A
----------------------------bev   ----------------------------elim
   λ x → t : (x : A) → B x                t u : B u

számítási és egyediség szabályok ugyanazok:
(λ x → t) u = t[x↦u]     (λ x → (f x)) = f


t : if x then ℕ else Bool, feltéve, hogy x : Bool

Agdában:

  Goal : if x then ℕ else Bool
  ______________________________________
  x : Bool

if x then 3 else true  <- értelmetlen, mert

t : Bool   u : A   v : A          x : Bool   3 : ℕ     true : Bool
------------------------          --------------------------------
if t then u else v : A

Bool szabályai:
---------------

  tipusbev:  Bool    : Set
  bev:       true    : Bool
             false   : Bool
  elim(ind): indBool : (P : Bool → Set) → P true → P false → (t : Bool) → P t
               (függő if-then-else-)
             if_then_else_ : {A:Set}→Bool → A     → A                    → A

             indBool (λ x → if x then ℕ else Bool) :
               ℕ → Bool → (t : Bool) → if t then ℕ else Bool

               (λ x → if x then ℕ else Bool) true = if true then ℕ else Bool=ℕ

             indBool (λ x → if x then ℕ else Bool) 3 true
               (x : Bool) → if x then ℕ else Bool

  számítási: indBool P u v true = u
             indBool P u v false= v

  (λ x → Eqb x true) : Bool → Set

             indBool-t egy predikátumra alkalmazom (unáris reláció)
-}
f : (x : Bool) → if x then ℕ else Bool
f = λ x → indBool (λ x → if x then ℕ else Bool) 3 true x

-- Eqb : Bool → Bool → Set
-- Eqb = λ a b → if a then (if b then ⊤ else ⊥) else (if b then ⊥ else ⊤)
{-
  Az Eqb függvény működése:

  Eqb true  true  = ⊤
  Eqb false false = ⊤
  Eqb true  false = ⊥
  Eqb false true  = ⊥

  tt : Eqb true true
  tt : Eqb false false
  ?  : Eqb true false

    halmazelméletben így írnánk: Eqb ⊆ Bool × Bool,
                                 Eqb = {(true,true), (false,false)}

tf : Eqb true false
tf = {!!}

tt' : Eqb true true
tt' = tt

ntf : ¬ Eqb false true -- ¬ Eqb false true = Eqb false true → ⊥ = ⊥ → ⊥
ntf = λ x → x

Agdában egy R : A → B → Set tekinthető bináris relációnak A-n és B-n
  (halmazelméletben R ⊆ A × B)

Agdában kétféle egyenlőség van.
= <- definíció szerinti egyenlőség (definitional equality, conversion, operational semantics)
     if true then u else v = u (számítási szabályok)
     rövidítések
  u = v az nem típus! (rövidítés létrehozása) nem kifejezhető Agdában belül:
       nem lehet feltételezni
       állításokban (típusokban) nem szerepelhet
       az Agda el tudja dönteni, hogy tetszőleges két term definió szerint
         egyenlő-e

  zero + t = t        zero + t = rec t suc zero = t
                                 rec t u v = v-ben a suc-okat u-ra, a zero-t t-re
                                 rec t u (suc (suc (suc zero)))=u(u(u t))
Eqb <- egyenlőség típus (Bool-ra)
  Eqb true false : Set ez TÍPUS, feltételezhető
  általánosságban az Agda nem tudja eldönteni, hogy bebizonyítható-e az 
    egyenlőség

f : (a : Bool) → Eqb true a → ℕ

indBool : (P : Bool → Set) → P true → P false → (t : Bool) → P t

reflexive : (b : Bool) → Eqb b b         -- ∀b.b=b
reflexive = indBool (λ x → Eqb x x) tt tt

függő szabályok természetes számokra:
tipusbev: ℕ    : Set
bev:  zero : ℕ
      suc  : ℕ → ℕ
elim: indℕ : (P : ℕ → Set)→ P zero → ({n : ℕ} → P n → P (suc n)) → (n : ℕ) → P n
      rec  : {A : Set}    → A      → (A → A)                     → ℕ → A
szam: indℕ P z s zero = z
      indℕ P z s (suc n) = s (indℕ P z s n)

  speciális eset:
      rec {A} = indℕ (λ _ → A)
      if_then_else_ {_}{A} t u v = indBool (λ _ → A) u v t
-}

not : Bool → Bool
not = λ a → if a then false else true
eqb : Bool → Bool → Bool
eqb = λ a b → if a then b else not b
Eqb = λ a b → if eqb a b then ⊤ else ⊥

pred : ℕ → ℕ ⊎ ⊤   -- Maybe ℕ
pred = rec (inj₂ tt) λ w → case w (λ n → inj₁ (suc n)) (λ _ → inj₁ 0)
{-
zero     = 0     inj₂ tt
suc zero = 1     inj₁ 0
2                inj₁ 1     
3                inj₁ 2
-}
eq0 : ℕ → Bool
eq0 = rec true (λ _ → false)

-- eq1
-- eq2
-- eq3

eqn : ℕ → ℕ → Bool
eqn = rec eq0 {!!}

Eqn : ℕ → ℕ → Set
Eqn = λ a b → if eqn a b then ⊤ else ⊥

refl-Eqn : (n : ℕ) → Eqn n n
refl-Eqn = {!!}
