open import Lib hiding (Fin; Σ; fst; snd; _,_)

-- Függő típusok
-- Egy típus függhet egy értéktől
--            ^ ezért függő

-- 0 : ℕ
-- 1 : ℕ
-- Mi a típusok típusa?
-- Set
-- ℕ : Set
-- Bool : Set
-- stb

-- Olyan fv-t szeretnék leírni, ami típusba képez, annak a típusa Set-re fog végződni.

f : Bool → Set -- 0,1 holeba típusokat kell írnom
f false = ℕ
f true = Bool → Bool

-- g : Bool → -- azt az első paraméter fel szeretném TÍPUSSZINTEN használni
g : (b : Bool) → f b -- itt annyit csináltam hogy az első paramétert elneveztem b-nek
g false = zero
g true = λ z → z

-- ELŐFELTÉTELEK ELKÓDOLÁSA
-- Minek KÉNE igaznak lennie ahhoz hogy egy függvény értelmes legyen
-- Pl.: half : ℕ → ℕ függvény nincs értelmezve páratlan számokra

badHalf : ℕ → ℕ
badHalf zero = zero
badHalf (suc zero) = zero -- 1 / 2 = 0
badHalf (suc (suc x)) = badHalf x

-- Ahhoz hogy mi egy ilyen esetet ki bírjunk szűrni, először meg kell tudnunk viszgálni hogy ilyen eset mikor áll fenn
isOdd : ℕ → Bool
isOdd zero = false
isOdd (suc zero) = true
isOdd (suc (suc x)) = isOdd x

-- Ezt a feltételt típusszinten el tudjuk kódolni.
-- Ötlet: Igazhoz valami triviális típust asszociálunk
-- Hamishoz meg egy olyan típust aminek nincs eleme

isEven' : ℕ → Set
isEven' zero = ⊤ -- triviális típus, pont 1 eleme van
isEven' (suc zero) = ⊥
isEven' (suc (suc x)) = isEven' x

half : (n : ℕ) → isEven' n → ℕ
half zero x = zero
-- ha az eset előjönne hogy half (suc zero)
-- olyan típusú paramétert kéne kapni
-- hogy isEven' (suc zero) ≡ ⊥
-- ⊥ típusú paraméter meg nem létezhet
half (suc (suc n)) x = half n x -- <- van extra paraméter amit tovább kell adogatni
-- x : isEven' n
-- => sok boilerplate

-- Vmi → Set típusú függvényeket hívják predikátumnak




-- explicit vs implicit paraméterek
-- explicit = olyan paraméterek amiket mindig meg kell adni
-- implicit = az Agda a kontextusból ki tudja őket találni (pl polimorfizmus)
-- id : {A : Set} → A → A
-- itt nem kell mindig megadnom hogy milyen típusra alkalmazom az id függvényt, mert az Agda a paraméterekből kitalálja

-- függőtípusosan modellezzünk típusokat úgy hogy le se lehessen rosszul írni a kifejezéseket
-- Vektor: egy olyan lista ami típusszinten indexelve van a hosszával (ezt hívják típuscsaládnak)

data Vector (A : Set) : ℕ → Set where
  [] : Vector A 0 -- Az üres lista hossza MINDIG 0
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (suc n) -- Az 1 vagy több elemeű lista hossza MINDING suc n
--       ^ implicit paraméter
--       azt jelenti nekünk hogy a _::_ jobb oldali paraméterének a hosszát az agda ki tudja találni

-- ∀{n} ≡ {n : Agda megoldja hogy mi a típusa}
---   V {A : Set} → {B : Set} → ...
map : {A B : Set}{n : ℕ} → (A → B) → Vector A n → Vector B n -- a map ne változtassa meg a vektor hosszát
map f [] = [] -- megköti ez az ág nekem azt hogy "len (Vector A n) = 0" => n = 0
map f (x ∷ vs) = f x ∷ map f vs -- megköti azt hogy a vektor hossza legalább 1, tehát n ~ suc n

-- alapból két megközelítése lehet ennek
-- 1. ha mindegyik vektor hossza megegyezik akkor nincs felesleges elem
--                                                      V            V            V
zipWith : {A B C : Set}{n : ℕ} → (A → B → C) → Vector A n → Vector B n → Vector C n
zipWith f [] [] = []
zipWith f (x ∷ vs) (x₁ ∷ vs') = f x x₁ ∷ zipWith f vs vs'

-- 2. (ezt nem fogjuk) haskell-féle: Egyszerűen csak eldobjuk a felesleget
-- Vector A n → Vector B k → Vector C (min n k)




-- Fin = Finite
-- Fin is egy típuscsalád = a típusban valami érték megjelenik
-- Fin k az mit jelent?
-- #1: A Fin k a K-nál kisebb számokat tartalmazza

-- Fin 0-nak mik lesznek az elemei?
-- NEM LESZ ELEME
-- Fin 1-nek mik lesznek az elemei?
-- fzero : Fin 1
-- Fin 2-nek mik lesznek az elemei?
-- fzero : Fin 2
-- fsuc fzero : Fin 2
-- .
-- .
-- .
---        V ℕ által indexelt
data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n) -- minden n esetén fzero : Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n) -- minden n esetén, ha van vmi f : Fin n, akkor fsuc f : Fin (suc n)

{-

Fin (n) | fzero | fsuc alkalmazva az elző sor elemeire
-------------------
0       |
1       | 0     |
2       | 0     | 1
3       | 0     | 1 2
-}

-- Fin k = k-nál kisebb számok
-- | Fin k | = k
-- | Vec A n | = n * | A |
-- érdekes elméleti feladat: (Vec ⊤ n) ↔ Fin n
-- Fin 0 ↔ ⊥
-- Fin 1 ↔ ⊤
-- Fin 2 ↔ Bool

-- Egy fontos dolgot vettünk fin-nel
_!!_ : {A : Set}{n : ℕ} → Vector A n → Fin n → A -- Mik azok az esetek amikor az indexelés nem lenne definiálva
-- n < 0 = ez Agdába nincs
-- n ≥ len (list) = ezt a Fin fogja nekünk megkötni, hiszem Fin n < n
-- _<_ : ℕ → ℕ → Set
-- (k : ℕ) → (k < n) → A
-- KISZŰRI A [] esetet. Ha [] eset lehetne, akkor lehetne n = 0 => Fin 0 típusú kifejezést kéne kapnom => olyan nincs
(x ∷ vs) !! fzero = x
(x ∷ vs) !! fsuc k = vs !! k
-- x ∷ vs : Vector A (suc n) ⇒ vs : Vector A n
-- fsuc k : Fin (suc n) ⇒ k : Fin n




-- Fin-nél
-- fzero azt mondja MINDEN n esetén fzero : Fin (suc n)
-- MINDEN kifejezés = UNIVERZÁLIS KVANTIFIKÁLÁS
-- mi lesz nekünk a LÉTEZIK / EXISZTENCIÁLIS KVANTOR?
-- Mi a lényege a "létezik" kifejezésnek
-- Agdában: Ha létezik olyan "a" elem hogy P(a), akkor explicit adjuk meg mi az az elem
-- Ez lesz a Σ típus

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    fst : A -- LÉTEZIK EZ AZ ELEM
    snd : B fst -- HOGY A MÁSODIK ÁLLÍTÁS IGAZ RÁ

--             V ez az analízis féle szumma
-- | Σ A P | = Σ (a ∈ A) | P a |

-- ∃ n ∈ ℕ: n osztható 2-vel
f1 : Σ ℕ λ n → isEven' n
f1 = 2 , tt -- ez lényegében egy tuple aminek a második paramétere függ az elsőtöl
