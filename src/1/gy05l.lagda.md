# Függő típusok

```agda
open import Lib hiding (fromℕ)
open import Lib.Containers.Vector hiding (head; tail; map; length; _++_)
open import Lib.Containers.List hiding (head; tail; map; length; _++_; filter)
```
## Vec and Fin

A `Vec` vagyis vektor az egy olyan adt típús, aminek típusában meg tudjuk szabni annak elemszámát.

Lényegét tekintve egy lista, aminek mindig pontosan tudjuk a hosszát.

A definíciója az alábbi:

```plaintext

infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

```

Látható az eddigitől eltérő `ℕ → Set` jelölés a data jobb oldalán. Ennek oka, hogy az adat struktúránk létrehozásához szükségünk van egy számra, a vektor hosszára.

A 0 hosszú vektor pontosan egy féleképpen konstruálható, az üres vektor konstruktorral.

Ha szeretnénk egy vektorhoz hozzáfűzni, akkor meg kell adnunk egy nála eggyel rövidebb listát, és az elemet, amit hozzá szeretnénk adni.

A következő feladatok a Vektor típus működését mutatják be.

A `head` és a `tail` függvények mind `suc n`-es vektort kérnek, ezáltal megszabtuk, hogy a lista nem lehet üres.

```agda

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ _) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (_ ∷ x) = x

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom zero = []
countDownFrom (suc n) = suc n ∷ countDownFrom n

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

```

Fin, vagyis Finite adat típus egy véges típus.

A típus konstruálásának a számát a típusban megadott szám határozza meg.

Tekinthetünk úgy a Fin-re, hogy egy torzított természetes szám, aminek megadjuk a maximumát.

Másikép még tekinthetünk rá úgy, mint egy halmazra, aminek megadtuk, pontosan hány eleme van.

A definíciója a következő:

```plaintext

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

```

A Fin elemeire láthatunk példát.

Hány eleme van a `Fin 0` típusnak?
És a `Fin 1`-nek? 

```agda

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = zero

f2-0 f2-1 : Fin 2
f2-0 = zero
f2-1 = suc zero

f3-0 f3-1 f3-2 : Fin 3
f3-0 = 0
f3-1 = 1
f3-2 = 2

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = zero
f4-1 = 2
f4-2 = suc zero
f4-3 = 3

```

A természetes számok, Fin és a Vektor kapcsolatára láthatunk a továbbiakban példát.

> Lib-ben a unicode ‼ az indexelés.

```agda

infixl 9 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
_!!_ (x ∷ _) zero = x
_!!_ (x ∷ xs) (suc m) = xs !! m

test-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ []) !! (suc (suc zero)) ≡ 1
test-!! = refl

test2-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ 0 ∷ 10 ∷ []) !! 3 ≡ 0 -- 3-as literál a !! után valójában Fin 5 típusú.
test2-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

map : {A B : Set}(f : A → B){n : ℕ} → Vec A n → Vec B n
map f {.0} [] = []
map f {.(suc _)} (x ∷ as) = f x ∷ map f as

```

A Lista definíciója. Látható, hogy sok eltérés nincsen a Vektorhoz képest.

```plaintext

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

```

```agda

length : {A : Set} → List A → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)

fromList : {A : Set}(as : List A) → Vec A (length as)
fromList [] = []
fromList (x ∷ as) = x  ∷ fromList as

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate {zero} _ = []
tabulate {suc n} f = f 0  ∷ tabulate {n} λ x → f (suc x)

```

## Szigma típus

Szigma típus az összeg típus általánosítása.

Legegyszerűbben úgy értelmezhető, mint a matematikau Szigma jelölés, ami szintén az összeget általánosítja Szummává.

A Szigma az első függőtípusos elemünk a kurzuson. Leegyszerűsítve a lényege ennyi: A szigma egy olyan rendezett pár, ahol a második elemnek a ***típusa*** függ az első elem ***értékétől***.

Egyszerű példát hivatott bemutatni a `simple1`, `simple2`, `simple3` függvények.

```agda

type : ℕ → Set
type zero = ⊤
type (suc x) = Bool

simple1 simple2 simple3 : ℕ → Σ ℕ λ x → type x
simple1 _ = 0 , tt
simple2 _ = 4 , true

simple3 x@(zero) = x , tt
simple3 x@(suc zero) = x , false
simple3 x@(suc (suc zero)) = x , true
simple3 x@(suc (suc y@(suc _))) = simple3 y

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ λ x → Vec A x
filter {A} {0} f [] = 0 , []
filter {A} {(suc n)} f (x ∷ xs) with f x
... | true = suc (fst (filter f xs)) , x ∷ snd (filter f xs)
... | false = filter f xs

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

```
