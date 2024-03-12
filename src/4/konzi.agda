module konzi where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

{-

C = Control
M = Alt

C-x C-f = Megnyit egy fájlt
C-g = Cancel
M-w = Copy
C-y = Paste
C-x u = Undo
C-w = Cut
C-a = Sor elejére ugrás
C-e = Sor végére ugrás
C-x h = Egész fájl kijelölése

C-c C-l = Typecheckeli a fájlt (és betölti)
C-c C-r = Refine (triviális dolgot belerak a lyukba)
C-c C-n = Normalise expression (kiértékelés)
C-c C-d = Infer type (visszadobja a kif típusát)
C-c C-SPC = Belerak lyukba adott kifejezést

\ = Unicode mode
\bN = ℕ

Divipp Agda Symbols: https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html
-}

-- 1. Óra

{-


  v 1 db :
f :: Int -> Int
f x = x + 1
-}

--  v \bN
f : Nat → Nat
--    ^ \to
f x = x + 1

-- Lambda kifejezések
-- λ x y → ...
-- ^ \Gl = Greek L, \lambda

f' : Nat → Nat
f' = λ x → x + 1

-- Parciális applikálás
-- Nem kell egyből minden paramétert megadni egy fgvnek

g : Nat → Nat → Nat
g x y = x + y

-- Magasabbrendű függvénynek
-- Ha fvt vár paraméterül

--   v fv paraméter
h : (Nat → Nat) → Nat
h f = f 4

-- h f' hogyan értékeli ki?
-- > Def behelyettesítés
-- (λ f → f 4) (λ x → x + 1)
-- > β-redukció
-- t = f 4
-- f-be helyettesítünk be
-- y = (λ x → x + 1)
-- (λ x → x + 1) 4
-- > β-redukció
-- 4 + 1
-- > elemi matematika
-- 5
{-

Lambdákra átírás
f x = .... ≡ f = λ x → ...

Definíció behelyettesítése
g = t

f = g ≡ f = t

Lambda számítási szabálya / β-redukció (β = \Gb, \beta)

(λ x → t) y ≡β t-be az x helyére behelyettesítünk y-t

(λ x → x + 1) 4 ≡β 4 + 1
t = x + 1
x-be helyettesítünk be
y = 4

Elemi matematikát
x + y az mennyi
x * y az mennyi

-}

-- Polimorfizmus
-- Tetszőleges típusra működő függvényt írunk
-- id : a -> a
-- annyi megkötés volt hogy a két a ugyanaz a típus
-- id : Int -> Int
-- id : Bool -> Bool

--   {implicit paraméter}
--   olyan paraméter amit nem veszünk fel az egyenlőség bal oldalán
--   Agda ki tudja inferálni a kontextusból hogy mi az
id : {A : Set} → A → A -- explicit paraméter
id x = x

id' : {A : Set} → A → A
id' = λ y → y
--    ^ ? = fájl betöltése
--    C-c C-, = mi kell a lyukba
--    C-c C-.
--    C-c C-r = triviális dolgot belerak a lyukba / ha megadunk valamit a lyukba akkor belerakja
--                                                  C-c C-SPC


--- Véges típusok
--- Mekkora egy típus mérete?
-- Hogyan definiálunk típusokat Agdában?
data Bool : Set where -- sorfolytonosan felsoroljuk a konstruktorait
  true : Bool
  false : Bool

-- |Bool| = 2, true és false



-- \x \times
-- Tuple, rendezett pár
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- |A|, minden a : A az összes B-t asszociálni tudom
{-
_| a₁ | a₂ | .....
b₁ t₁₁  t₁₂ ....
-
b₂ t₂₁  t₂₂
-
.
.
.
-}
-- |A × B| = |A| · |B|

-- Top, \top
data ⊤ : Set where
  tt : ⊤

-- |⊤| = 1

-- Bottom, \bot
data ⊥ : Set where -- nincs konstruktora ⇒ nincs eleme
-- |⊥| = 0

-- \uplus, \u+ -- kis u! \U+ ⊎⨄
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
-- |A ⊎ B| = |A| + |B|

-- |A → B| = ?, mi is számít külön függvénynek?
-- λ x → x ≟ λ y → y ✓ <--- α-ekvivalencia
-- λ { true → true ; false → false } ≟ λ x → x ✓
-- Függvény extencionalitás (extensionality)
-- ∀ x. f(x) = f(g) ⇒ f = g
-- |A → B| = |B| ^ |A|

-- \lr
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A) -- nagyon informálisan, ha |A| = |B|, akkor A ↔ B és fordítva


case : {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
case (inl a) a→c b→c = a→c a -- caseβ₁
case (inr b) a→c b→c = b→c b -- caseβ₂

exfalso : {A : Set} → ⊥ → A
exfalso ()

-- |A| = |A ⊎ ⊥|
-- |A| = |A| + 0
lemma : {A : Set} → A ↔ (A ⊎ ⊥)
lemma = (λ x → inl x) , λ x → case x (λ z → z) exfalso


-- Induktív típusok
-- Voltak ℕ-ok
-- Hogyan definiáljuk őket?
{-
Teljes indukció koncepcióját
P(0)
P(n) ⇒ P(n+1)
∀n. P(n)
-}

data ℕ : Set where
  zero : ℕ -- zero létezik
  suc  : ℕ → ℕ -- ha n létezik, akkor n + 1 is
  -- ahány suc van, annyi a ℕ értéke
--                                                  ^
five : ℕ --                                         |
five = suc (suc (suc (suc (suc zero)))) --          |
--                                                  |
-- Strukturális indukció  --------------------------|
-- Indukciós hipotézis
-- Induction principle

times2 : ℕ → ℕ -- x * 2, C-c C-c <paramnév> ENTER, az mintailleszt <paramnév>-re
times2 zero = zero -- 0 * 2 ≟
times2 (suc x) = suc (suc (times2 x))
-- Ha tudjuk hogy P(n) mennyi, akkor P(n+1)-et is tudjuk
-- P(n) = times2 x, 2 * x, 2 * (x + 1)
-- 2 * (x + 1)
-- [2 * x] + 2

times3 : ℕ → ℕ
times3 zero = zero -- 0 * 3
times3 (suc x) = suc (suc (suc (times3 x))) -- ind hipo: times3 x azaz x * 3, (x + 1) * 3 = [x * 3] + 3

div2 : ℕ → ℕ
div2 zero = zero -- 0 / 2
div2 (suc zero) = zero -- 1 / 2
div2 (suc (suc x)) = suc (div2 x)
-- (1 + x) / 2, x / 2
-- 1 / 2 + [x / 2]
-- (2 + x) / 2 = 1 + [x / 2]

_++_ : ℕ → ℕ → ℕ -- x-re, y-ra vagy mindkettőre?
zero ++ y = y -- 0 + y?
suc x ++ y = suc (x ++ y)

{-
0 + 0 = 0
0 + suc x = suc x
suc y + 0 = suc y
suc y + suc x = suc (suc (y + x))

-}

-- x + y
-- (1 + x) + y

{-

Definicionális Egyenlőség
0 + x ≟ x
1 + x ≟ suc x
x + 0 ≟ x
-}

lemma0 : {x : ℕ} → zero ++ x ≡ x
lemma0 = refl

lemma1 : {x : ℕ} → suc zero ++ x ≡ suc x
lemma1 = refl

lemma2 : {x : ℕ} → x ++ zero ≡ x
lemma2 = {!!}
