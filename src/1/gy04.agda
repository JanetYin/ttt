module gy04 where

open import Lib hiding (_+∞_; coiteℕ∞)

open import Lib.Containers.List hiding (zipWith; head; tail; length; map; _++_; iteList; take)
open import Lib.Containers.Stream hiding (zipWith; coiteStream; map; _++_)

---------------------------------------------------------
-- típusok η-szabályai
---------------------------------------------------------
{-
Emlékeztető: A η-szabály azt mondja meg, hogy mit tegyünk, ha destruktorra alkalmazunk konstruktort.
Pl. függvények esetén (λ a → f a) ≡ f, ahol a függvényalkalmazás a destruktor és a λ a konstruktor.

Természetesen más típusoknak is ugyanúgy van η-szabálya.

Vegyük példaként a ⊤-ot:
Destruktora: ite⊤ : A → ⊤ → A

Ez alapján az η-szabály az alábbi lesz:
ite⊤ tt ≡ λ x → x

Ez természetesen Agdában bizonyítható is.
-}

ite⊤ : ∀{i}{A : Set i} → A → ⊤ → A
ite⊤ x _ = x

⊤η : ∀{x} → ite⊤ tt x ≡ x
⊤η = refl

{-
Ahogy emlékeztek rá, a ⊤ η-szabálya úgy néz ki, hogy ∀ a → a ≡ tt,
tehát itt is igaz lesz, hogy egy típusnak több egymással ekvivalens η-szabálya lehet.

Nézzük újra példaként a Bool típust. A β-szabályai a következők voltak:
if false then u else v ≡ u
if true then u else v ≡ v

Mi lehet az η-szabály? Hogy lehet "destruktorra alkalmazni konstruktort" ilyen esetben?
Az if_then_else_ esetén a "then" és az "else" ágban lévő dolgok tetszőleges értékek lehetnek;
ide akár konstruktort is be lehet írni. Tehát úgy lehet felépíteni az η-szabályokat, hogy a destruktor megfelelő
helyeire beírom az azonos típus konstruktorait.
Bool esetén ez azt jelenti, hogy az if_then_else_-ben a második és harmadik helyre kell a Bool két konstruktorát írni.
Ezen felül úgy kell beírni a két konstruktort, hogy alapvetően az "identitás" függvényt kapjuk az adott típuson.
Bool esetén tehát úgy kell az if_then_else_-et felparaméterezni, hogy a false-ra false legyen az eredmény, true-ra pedig true.

Ez alapján mi lesz a Bool-oknak egy lehetséges η-szabálya?
Válasz: if_then true else false = λ b → b

Ugyanezt az ismert 𝟛 típuson is el lehet játszani.
data 𝟛 : Set where
  a1 a2 a3 : 𝟛

Ismert a destruktor: ite𝟛 : A → A → A → 𝟛 → A

Mi lesz a 𝟛 η-szabálya?
Válasz: ite𝟛 a1 a2 a3 ≡ λ b → b

Természetes számokon a helyzet szintén nem változik.
Ismert a destruktor: iteℕ : A → (A → A) → ℕ → A

Mi lesz ℕ η-szabálya?
Válasz: iteℕ zero suc ≡ λ n → n

-}

---------------------------------------------------------
-- positivity
---------------------------------------------------------

-- Miért nem enged agda bizonyos típusokat definiálni? Pl. alapesetben az alábbit sem.

{-# NO_POSITIVITY_CHECK #-}
data Tm : Set where
  lam : (Tm → Tm) → Tm

-- FELADAT: Tm-ből adjuk vissza a lam értékét.
app : Tm → (Tm → Tm)
app = {!!}

self-apply : Tm
self-apply = lam (λ t → app t t)

-- C-c C-n this:
Ω : Tm
Ω = app self-apply self-apply

{-# NO_POSITIVITY_CHECK #-}
data Weird : Set where
  foo : (Weird → ⊥) → Weird
  -- Hogy kell elolvasni magyarul a "foo" konstruktort?

unweird : Weird → ⊥
unweird = {!!}

-- ⊥ típusú értéknek TILOS léteznie, ellenkező esetben a rendszer inkonzisztens, nem használható SEMMIRE.
bad : ⊥
bad = {!!}

---------------------------------------------------------
-- lists
---------------------------------------------------------

{-
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
infixr 5 _∷_
-}

-- FELADAT: Határozzuk meg egy lista elemszámát!
length : {A : Set} → List A → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)

length-test1 : length {ℕ} (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
length-test1 = refl
length-test2 : length {ℕ} (1 ∷ []) ≡ 1
length-test2 = refl

-- FELADAT: Adjuk össze egy lista számait.
sumList : List ℕ → ℕ
sumList [] = 0
sumList (x ∷ xs) = x + sumList xs

sumList-test : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
sumList-test = refl

-- FELADAT: Fűzzünk össze két listát!
_++_ : {A : Set} → List A → List A → List A
_++_ = {!!}
infixr 5 _++_

++-test : the ℕ 3 ∷ 2 ∷ [] ++ 1 ∷ 4 ∷ [] ≡ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []
++-test = refl

-- FELADAT: Alkalmazzunk egy függvényt egy lista minden elemén!
map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-test : map (_+ 2) (3 ∷ 9 ∷ []) ≡ (5 ∷ 11 ∷ [])
map-test = refl

-- FELADAT: Definiáld a lista eliminátorát! Dolgozzunk fel egy listát:
-- ha üres a lista, akkor csak adjunk vissza egy alapértéket
-- ha a listában van elem, akkor alkalmazzunk rá egy függvényt az alapértékkel úgy, hogy az kifejezés jobbra legyen zárójelezve.
-- Haskell-ben foldr
-- Hány paraméteres lesz a függvény?
iteList : {A B : Set} → B → (A → B → B) → List A → B    
iteList b f [] = b
iteList b f (x ∷ xs) = f x (iteList b f xs)
{-
iteList-test1 : iteList 3 _^_ (2 ∷ 3 ∷ []) ≡ 2 ^ 27
iteList-test1 = refl
-}

iteList-test2 : iteList {ℕ} [] _∷_ (1 ∷ 2 ∷ 3 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
iteList-test2 = refl

-- FEL: add meg a fenti fuggvenyeket (length, ..., map) iteList segitsegevel!

---------------------------------------------------------
-- coinductive types
---------------------------------------------------------

{-
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream
-}
-- check that the type of head : Stream A → A
--                        tail : Stream A → Stream A

-- Ez a típus lényegében a végtelen listákat kódolja el.
-- Ebben véges lista nincs benne, csak végtelen!


-- Copattern matching!
-- FELADAT: Add meg azt a végtelen listát, amely csak 0-kból áll.
zeroes : Stream ℕ
head zeroes = 0
tail zeroes = zeroes
-- Honnan tudja agda, hogy ez totális?
-- Termination checker nem tud futni, hiszen a lista végtelen.
-- Productivity checker

-- by pattern match on n
-- FELADAT: Add meg azt a listát, amely n-től 1-ig számol vissza egyesével.
countDownFrom : ℕ → List ℕ
countDownFrom zero = []
countDownFrom (suc n) = suc n ∷ countDownFrom n

-- from n is not by pattern match on n
-- copattern match on Stream
-- FELADAT: Adjuk meg azt a végtelen listát, amely n-től 1-esével felfelé számol!
from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (suc n)

-- pointwise addition
zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

-- Definiálható-e a filter sima listákon?
filterL : {A : Set} → (A → Bool) → List A → List A
filterL p [] = []
filterL p (x ∷ xs) = let r = filterL p xs in if p x then x ∷ r else r

-- Definiálható-e a filter Stream-eken?
-- Nem
{-
filterS : {A : Set} → (A → Bool) → Stream A → Stream A
head (filterS p xs) = if p (head xs) then head xs else head (filterS p (tail xs))
                                                       ^^^^ -- nem fogyott destruktor
tail (filterS p xs) = {!!}
-}
-- one element from the first stream, then from the second stream, then from the first, and so on
interleave : {A : Set} → Stream A → Stream A → Stream A
head (interleave xs ys) = head xs
tail (interleave xs ys) = interleave ys (tail xs)

{-
interleave : {A : Set} → Stream A → Stream A → Stream A
head (interleave xs ys) = head xs
head (tail (interleave xs ys)) = head ys
tail (tail (interleave xs ys)) = interleave (tail xs) (tail ys)
-}
-- get the n^th element of the stream
get : {A : Set} → ℕ → Stream A → A
get zero xs = head xs
get (suc n) xs = get n (tail xs)

-- byIndices [0,2,3,2,...] [1,2,3,4,5,...] = [1,3,4,2,...]
byIndices : {A : Set} → Stream ℕ → Stream A → Stream A
byIndices = {!!}

-- iteℕ : (A : Set) → A → (A → A)  → ℕ → A
--        \______________________/
--         ℕ - algebra

-- head : Stream A → A
-- tail : Stream A → Stream A
-- Mi lesz a Stream konstruktora?
coiteStream : {A B : Set} → (B → A) → (B → B) → B → Stream A
--               \______________________________/
--                        Stream A - coalgebra
head (coiteStream h t s) = h s
tail (coiteStream h t s) = coiteStream h t (t s)

-- ex: redefine the above functions using coiteStream

-- A fájl tetején lévő leírás alapján természetesen a Stream-nek is megadható az η-szabálya.
-- Megjegyzés: Típuselméleti "gondok" miatt MLTT-ben ez már egy nem bizonyítható állítás lesz.
-- (Teljesül, csak az MLTT képtelen a bizonyítására, ez abban látszódik meg, hogy se bizonyítani, se cáfolni nem lehet.)
Stream-η : {A : Set}(s : Stream A) → coiteStream head tail s ≈S s
head-≡ (Stream-η s) = refl
tail-≈ (Stream-η s) = Stream-η (tail s)

-- ex: look at conatural numbers in Thorsten's book and do the exercises about them

-- simple calculator (internally a number, you can ask for the number, add to that number, multiply that number, make it zero (reset))
record Machine : Set where
  coinductive
  field
    getNumber : ℕ
    add       : ℕ → Machine
    mul       : ℕ → Machine
    reset     : Machine
open Machine

calculatorFrom : ℕ → Machine
calculatorFrom n = {!!}

c0 c1 c2 c3 c4 c5 : Machine
c0 = calculatorFrom 0
c1 = add c0 3
c2 = add c1 5
c3 = mul c2 2
c4 = reset c3
c5 = add c4 2

-- FELADAT: Készítsünk egy csokiautomatát.
-- A gépbe tudunk pénzt dobálni (ez legyen ℕ, ennyit adjunk hozzá a jelenlegi kreditünhöz).
-- A tranzakciót meg tudjuk szakítani, a kredit 0 lesz és visszaadja a pénzünket.
-- Legyen 3 termékünk, ezek egyenként kerülnek valamennyibe és van belőlük a gépben valamennyi.
-- + Twix: 350-be kerül, kezdetben van a gépben 50 darab.
-- + Croissant: 400-ba kerül, kezdetben van 75 darab.
-- + Snickers: 375-be kerül, kezdetben van 60 darab.
-- Tudunk 1 terméket vásárolni, ha van elég bedobott pénzünk, ekkor a darabszámból vonjunk le egyet (ha lehet) és adjuk vissza a visszajárót, a kreditet nullázzuk le.
-- A gép tartalmát újra tudjuk tölteni, ekkor twix-ből legyen újra 50 darab, croissant-ból 75, snickers-ből pedig 60.



-----------------------------------------------------
-- conatural numbers
-----------------------------------------------------
{-
record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞
open ℕ∞
-}

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
_+∞_ = {!!}

-- Ez a függvény létezik, ezzel lehet megnézni
-- egy conat tényleges értékét.
-- Az első paraméter a fuel, maximum ezt a természetes számot tudja visszaadni.
-- Második paraméter a conat, amire kíváncsiak vagyunk.
-- Értelemszerűen ∞-re mindig nothing az eredmény.
{-
ℕ∞→ℕ : ℕ → ℕ∞ → Maybe ℕ
ℕ∞→ℕ zero _ = nothing
ℕ∞→ℕ (suc n) c with pred∞ c
... | zero∞ = just 0
... | suc∞ b with ℕ∞→ℕ n b
... | nothing = nothing
... | just x = just (suc x)
-}

coiteℕ∞ : {B : Set} → (B → Maybe B) → B → ℕ∞
coiteℕ∞ = {!!}

-- TODO, further exercises: network protocols, simple machines: chocolate machine (input: coin, getChocolate, getBackCoins, output: error, chocolate, money back), some Turing machines, animations, IO, repl, shell
