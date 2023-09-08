module hf02 where

open import lib

-- Ezt már megcsináltuk gyakorlaton.
assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = to' , from' where
  to' : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  to' (inl (inl x)) = inl x
  to' (inl (inr x)) = inr (inl x)
  to' (inr x) = inr (inr x)

  from' : {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
  from' (inl x) = inl (inl x)
  from' (inr (inl x)) = inl (inr x)
  from' (inr (inr x)) = inr x

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = {!!}

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = {!!}

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = {!!}

-- (×, ⊤) kommutatív egységelemes félcsoport

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = {!!}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = {!!}

idr× : {A : Set} → A × ⊤ ↔ A
idr× = {!!}

-- ⊥ egy null elem

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = {!!}

-- disztributivitása a × és az ⊎-nak.

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!!}

-- hatványozás törvényei

-- Cᴬˣᴮ = (Cᴬ)ᴮ
curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
curry = {!!}

-- Cᴬ⁺ᴮ = Cᴬ * Cᴮ
⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!!}

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
law^0 = {!!}

law^1 : {A : Set} → (⊤ → A) ↔ A
law^1 = {!!}

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = {!!}

-- (A + B)² = A² + 2AB + B²
iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
iso1 = {!!}

iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
iso2 = {!!}

iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ Bool ⊎ ⊤
iso3 = {!!}
testiso3 : fst iso3 (inl tt) ≢ fst iso3 (inr (inl tt))
testiso3 ()
testiso3' : fst iso3 (inl tt) ≢ fst iso3 (inr (inr tt))
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≢ fst iso3 (inr (inr tt))
testiso3'' ()

iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ (⊤ ⊎ ⊤)
iso4 = {!!}
testiso4 : fst iso4 (λ _ → inl tt) ≢ fst iso4 (λ _ → inr (inr tt))
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≢ snd iso4 (inr tt) tt
testiso4' ()

------------------------------------------
-- Magyarázat még a definícionális egyenlőségről:
-- Vegyük az alábbi példát:

_∧₁_ : Bool → Bool → Bool
true ∧₁ true = true
_    ∧₁ _    = false -- a sor elejét agda kiemeli, mert átfedés van az esetek között

_∧₂_ : Bool → Bool → Bool
true ∧₂ b = b
false ∧₂ _ = false
{-
Mi a különbség a két definíció között?
Első ránézésre semmi, mindkettő pontosan ugyanúgy működik.
Azonban ha elkezdünk egy kicsit játszani a két éssel, rögtön kiderül,
hogy különbség nagyon is sok van közöttük, a két függvény teljesen másképp
működik, ebből következően teljesen másképp viselkedik.
Nézzünk példákat erre, hogy is látszódik ez meg.
-}

∧₁-ex1 : true ∧₁ true ≡ true
∧₁-ex1 = refl
-- Ebben semmi meglepő nincs, maga ez a sor a definícióban is ott van.

∧₂-ex1 : true ∧₂ true ≡ true
∧₂-ex1 = refl
-- Definíció szerint az lesz az eredmény, amit a második paraméter helyére
-- helyettesítek.

∧₁-ex2 : true ∧₁ false ≡ false
∧₁-ex2 = refl

∧₂-ex2 : true ∧₂ false ≡ false
∧₂-ex2 = refl
-- Amíg a két érték egyértelműen adott,
-- addig semmi különbséget nem fogunk tapasztalni.

-- Nézzünk egy érdekesebb esetet, ahol érdekességekkel tudunk találkozni.
∧₁-ex3 : (λ a → false ∧₁ a) ≡ (λ a → false)
∧₁-ex3 = refl

∧₂-ex3 : (λ a → false ∧₂ a) ≡ (λ a → false)
∧₂-ex3 = refl
-- Ez az eset még mindig jól működik, definíció szerint ha az első paraméter nem true,
-- akkor az csak false lehet, és abban az esetben az eredmény false,
-- tehát agda ekkor még tud normalizálni.

-- Az alábbi példában találkozunk az igazi érdekességgel.
∧₁-ex4 : (λ a → true ∧₁ a) ≡ (λ a → a)
∧₁-ex4 = {! refl !}

∧₂-ex4 : (λ a → true ∧₂ a) ≡ (λ a → a)
∧₂-ex4 = refl
-- Az ∧₁-es egyenlőség már nem fog teljesülni definíció szerint,
-- mert a második paraméterről is egyértelműen tudni kell, hogy micsoda.
-- Ha megpróbáljuk az ∧₁-es egyenlőséget refl-lel bizonyítani, akkor fordítási hibát kapunk:
-- true ∧₁ a ≠ a of type Bool
-- (Az ∧₁-es egyenlőség bizonyíthatóan teljesül, de nem definíció szerint.)

-- Az ∧₂-es egyenlőség ezzel szemben definíció szerint teljesülni fog, pont így van definiálva,
-- csak az első paramétertől függ, hogy a függvény miként viselkedik.

-- Éppen ezért érdemes a függvényeket megpróbálni úgy definiálni, hogy minél
-- kevesebb paraméterre kelljen mintailleszteni, mert akkor több eset fog definíció szerint működni,
-- amelynél agdában nincs jobb működés.
------------------------------------------
-- ⊤ ⊎ ⊤ féle Bool.

Bool' : Set
Bool' = ⊤ ⊎ ⊤

-- Nem kötelező, de egyszerűség kedvéért lehet megadni agdában
-- saját mintákat a "pattern" kulcsszó használatával.
{-
pl.
pattern trivial = tt
f : ⊤ × ⊤ → ⊤ × ⊤
f (trivial , tt) = tt , trivial

Definiálj saját mintákat, amelyeknek ⊤ ⊎ ⊤ a típusa,
az egyik neve legyen False, amely legyen az (inl tt),
a másik legyen True, amely legyen az (inr tt) a tesztek miatt.
(Nyilván nagybetűkkel, mert a kisbetűsök már foglaltak.)
-}

-- Definiáld az if_then_else'_ függvényt, amely a ⊤ ⊎ ⊤
-- típussal definiálja a Bool típust.
-- Add meg a függvény típusát is úgy, hogy a Bool'-t használja!
-- A második és harmadik paraméterek tetszőlegesek, de azonos
-- típusúaknak kell lenniük.
if_then_else'_ : {A : Set} → Bool' → A → A → A
if b then x else' y = {!   !}

if-then-else-test1 : {A : Set}{x y : A} → if (inr tt) then x else' y ≡ x
if-then-else-test1 = refl

if-then-else-test2 : {A : Set}{x y : A} → if (inl tt) then x else' y ≡ y
if-then-else-test2 = refl

-- Definiáld az alábbi logikai függvényeket, amelyek szintén Bool'-t használnak:
-- Add meg a függvények típusait is!
-- Ha a második paraméter változó, a megfelelő módon akkor is legyenek definícionális egyenlőségek.
-- Tehát a második paraméter mindig maradjon változó és úgy legyenek definiálva a függvények.
¬'_ : Bool' → Bool'
_∧'_ _∨'_ _⊃'_ : Bool' → Bool' → Bool'

¬' b = {!   !}

a ∧' b = {!   !}
a ∨' b = {!   !}
a ⊃' b = {!   !}

¬-test-1-2 : (¬' (inl tt) ≡ inr tt) × (¬' (inr tt) ≡ inl tt)
¬-test-1-2 = refl , refl

∧-test-1 : (λ a → inr tt ∧' a) ≡ (λ a → a)
∧-test-1 = refl

postulate
  funExt : ∀{i j} {A : Set i} {B : A → Set j} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

∧-test-2 : (λ a → a ∧' inl tt) ≡ (λ a → inl tt)
∧-test-2 = funExt λ { (inl tt) → refl
                    ; (inr tt) → refl}

∧-test-3 : (λ a → inl tt ∧' a) ≡ (λ a → inl tt)
∧-test-3 = refl
--------------------------------------------------
{-
Definiálj 3 értékű logikai típust 3Bool névvel datát használva!
A három értéke legyen no, undefined, yes.
-}



{-
Definiáld a 3 értékű logika műveleteit ¬3_, _∧3_, _∨3_, _⊃3_ nevekkel.
A műveletek igazságtáblái az alábbiak:
(F = false, U = undefined, T = true)
A | ¬3 A        ∧3 | F | U | T    ∨3 | F | U | T
F |   T         F  | F | F | F    F  | F | U | T
U |   U         U  | F | U | U    U  | U | U | T
T |   F         T  | F | U | T    T  | T | T | T

⊃3 | F | U | T
F  | T | T | T
U  | U | U | T
T  | F | U | T
-}

-- Add meg a függvények típusait is!

-------------------------------------------------------------------------------
-- Bizonyítsd be, hogy 3Bool izomorf a Bool ⊎ ⊤ típussal.
-- Izomorfizmus bizonyításához szükséges logikai ekvivalencia,
-- illetve az oda-vissza "járkálás" bármilyen sorrendben
-- mindig a kezdeti elemet adja vissza.

-- (A gyakorlatban ennek a függvénynek értelmesebb neve lenne,
-- de akkor lelőném, hogy mit kéne típusként felírni.)
-- Használd a gyakorlaton látott átlátást segítő where blokkot,
-- illetve a to és from függvényeket is definiáld!
{- ⟵ ezt a komment kezdő jelet ki kell törölni, meg a fájl legvégén lévő zárót is, illetve ezt a szöveget is.
3↔2+1 : 3Bool ↔ Bool ⊎ ⊤
3↔2+1 = ?

-- Az alábbi lyukak mindegyikét ki lehet tölteni a C-c C-r
-- gombkombináció használatával. Ha nem lehet, akkor a fentebbi
-- logikai ekvivalencia nem helyes, mert nem izomorf.
proof₁ : snd 3↔2+1 (fst 3↔2+1 no) ≡ no
proof₁ = ?

proof₂ : snd 3↔2+1 (fst 3↔2+1 undefined) ≡ undefined
proof₂ = ?

proof₃ : snd 3↔2+1 (fst 3↔2+1 yes) ≡ yes
proof₃ = ?

proof₄ : fst 3↔2+1 (snd 3↔2+1 (inl false)) ≡ inl false
proof₄ = ?

proof₅ : fst 3↔2+1 (snd 3↔2+1 (inl true)) ≡ inl true
proof₅ = ?

proof₆ : fst 3↔2+1 (snd 3↔2+1 (inr tt)) ≡ inr tt
proof₆ = ?
ezt is ki kell törölni ezen szöveggel együtt → -}
---------------------------------------------------------
{-
Hány eleműek az alábbi típusok?
(A lib-ben is megnézhető, az ⊎, →, × mind jobbra zárójeleznek,
továbbá az operátorok erőssége csökkenő sorrendben: ×, ⊎, →)

Bool ⊎ Bool
Bool × Bool
Bool × Bool × Bool
Bool → Bool
Bool → Bool → Bool
Bool ↔ Bool
⊤ × ⊥
⊤ → ⊥
⊥ → ⊥
⊥ ↔ ⊥
(⊤ ⊎ Bool × ⊥) ↔ (Bool × ⊤)
(Bool ⊎ ⊤ × ⊥) ↔ (Bool × ⊤)
-}