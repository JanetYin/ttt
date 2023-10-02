# Véges típusok

- Véges típus
   - A típusokra halmazokhoz hasonlítjuk
   - Egy típus számossága megegyezik a konstruktorainak számával ~~azok számosságának összegével~~.
      - Pl: Bool számossága 2, ℕ számossága megszámlálhatóan végtelen
   - Ezekkel műveletek is végezhetőek
- Végtelen típusok ~~Koinduktivítás~~
   - ???

> Szorzat típus:
> - Haskell: touple/kettős
> - Mind a két típusból meg kell adni elmet
> - `×`-szel adjuk meg a típusát
> - `_,_`-vel tudod létrehozni
> - Szorzat, mivel a számossága megegyezik a megadott típusok számosságának szorzatával. (`c = a * b` ahol `c` a szorzat típus számossága, `a` a kettős első típusának, `b` a kettős második típusának számossága.)

```agda
open import Lib hiding (comm⊎)

flip : ℕ × Bool → Bool × ℕ
flip (fst , snd) = (snd , fst)

flipback : Bool × ℕ → ℕ × Bool
fst (flipback x) = snd x
snd (flipback x) = fst x

comm× : {A B : Set} → A × B → B × A
comm× (fst , snd) = snd , fst

comm×back : {A B : Set} → B × A → A × B
comm×back = comm×

```

> `⊤` : Az a típus, aminek pontosan egy konstruktora/eleme van. Ez a `tt`.

> Összeg típus:
> - Haskell: Either, ~~Maybe~~
> - Csak az egyik típusból kell megadni elemet
> - `⊎`-val adjuk meg a típusát
> - Két módon tudod létrehozni `inr` és `inl`.
> - Összeg típus, mivel a számossága a megadott típusok számosságának összege. (`c = a + b` ahol `c` a szorzat típus számossága, `a` az első típusának, `b` a második típusának számossága.)

```plaintext

S(x) = x típus számossága

Bool × ⊤ ~> S(Bool) * S(⊤) = 2 * 1 = 2

⊤ ⊎ ⊤ ~> S(⊤) + S(⊤) = 1 + 1 = 2

Bool ⊎ ⊤ ~> S(Bool) + S(⊤) = 2 + 1 = 3

```

```agda

b1 b2 : Bool × ⊤
b1 = true , tt
b2 = false , tt
b1≠b2 : b1 ≡ b2 → ⊥
b1≠b2 ()

t1 t2 : ⊤ ⊎ ⊤
t1 = inr tt
t2 = inl tt
t1≠t2 : t1 ≡ t2 → ⊥
t1≠t2 ()

bb1 bb2 bb3 : Bool ⊎ ⊤
bb1 = inr tt
bb2 = inl true
bb3 = inl false
bb1≠bb2 : bb1 ≡ bb2 → ⊥
bb1≠bb2 ()
bb1≠bb3 : bb1 ≡ bb3 → ⊥
bb1≠bb3 ()
bb2≠bb3 : bb2 ≡ bb3 → ⊥
bb2≠bb3 ()

```

> Nyíl operátor
> - A függvényeket ezzel hozzuk létre
> - Hatványozás műveletét rejti magában
> - A → B ~> S(B) ^ S(A)

```plaintext

A × A ~> S(A) * S(A) = a * a = a ^ 2

Bool → A ~> S(A) ^ S(Bool) = a ^ 2

```

```agda

-- Melyiket tudjuk megadni?
-- Topból bottomot tudunk létrehozni? Nem.
-- Bottomból tudunk topot létrehozni? Igen!
ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)
ee = inr λ x → tt

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = inl tt , (inl tt)

from' : {A : Set} → A × A → (Bool → A)
from' (fst₁ , snd₁) false = snd₁
from' (fst₁ , snd₁) true = fst₁
to' : {A : Set} → (Bool → A) → A × A
to' = λ f → f true , f false
testfromto1 : {A : Set}{a b : A} → fst (to' (from' (a , b))) ≡ a
testfromto1 = refl
testfromto2 : {A : Set}{a b : A} → snd (to' (from' (a , b))) ≡ b
testfromto2 = refl
testfromto3 : {A : Set}{a b : A} → from' (to' (λ x → if x then a else b)) true ≡ a
testfromto3 = refl
testfromto4 : {A : Set}{a b : A} → from' (to' (λ x → if x then a else b)) false ≡ b
testfromto4 = refl

```

## Az összes algebrai törvény

> (⊎, ⊥) kommutativ egysegelemes felcsoportot alkot.
> Vagyis asszociativítást, "egység elemmel", másképpen null elemmel való összeadást, és kommutativítást mutatjuk meg.

### Összeadás

```agda

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
fst assoc⊎ (inl (inl a)) = inl a
fst assoc⊎ (inl (inr b)) = inr (inl b)
fst assoc⊎ (inr b) = inr (inr b)
snd assoc⊎ (inl a) = inl (inl a)
snd assoc⊎ (inr (inl a)) = inl (inr a)
snd assoc⊎ (inr (inr b)) = inr b

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
fst idl⊎ (inr b) = b
snd idl⊎ x = inr x

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
fst idr⊎ (inl a) = a
snd idr⊎ = inl

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
fst comm⊎ (inl a) = inr a
fst comm⊎ (inr b) = inl b
snd comm⊎ (inl a) = inr a
snd comm⊎ (inr b) = inl b

```

### Szorzás

> (×, ⊤) kommutativ egysegelemes felcsoport alkot.

```agda

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
fst assoc× ((fst₁ , snd₂) , snd₁) = fst₁ , snd₂ , snd₁
snd assoc× (fst₁ , fst₂ , snd₁) = (fst₁ , fst₂) , snd₁

idl× : {A : Set} → ⊤ × A ↔ A
fst idl× (fst₁ , snd₁) = snd₁
snd idl× x = tt , x

idr× : {A : Set} → A × ⊤ ↔ A
fst idr× (fst₁ , snd₁) = fst₁
snd idr× x = x , tt

```

> ⊥ a nulla számosságú típus

```agda

null× : {A : Set} → A × ⊥ ↔ ⊥
fst null× x = snd x
snd null× x = exfalso x , x

```


## Következő órán folytatjuk!

> × és ⊎ disztributívitása

```agda

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
fst dist (fst₁ , inl a) = inl (fst₁ , a)
fst dist (fst₁ , inr b) = inr (fst₁ , b)
snd dist (inl (fst₁ , snd₁)) = fst₁ , inl snd₁
snd dist (inr (fst₁ , snd₁)) = fst₁ , inr snd₁

```

> exponenciális szabályok

```agda

curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
fst curry x x₁ x₂ = x (x₁ , x₂)
snd curry x (fst₁ , snd₁) = x fst₁ snd₁

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
fst ⊎×→ x₁ = (λ x → x₁ (inl x)) , λ x → x₁ (inr x)
snd ⊎×→ (fst₁ , snd₁) (inl a) = fst₁ a
snd ⊎×→ (fst₁ , snd₁) (inr b) = snd₁ b

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
fst law^0 x = tt
snd law^0 x x₁ = exfalso x₁

law^1 : {A : Set} → (⊤ → A) ↔ A
fst law^1 x = x tt
snd law^1 x x₁ = x

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
fst law1^ x = tt
snd law1^ x x₁ = x

```

## random izomorfózis

```agda
iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
fst (iso1 {A} {B}) x = f (x true) (x false) where
  f : A ⊎ B → A ⊎ B → _
  f (inl a) (inl a₁) = inl λ where
      true -> a
      false -> a₁
  f (inl a) (inr b) = inr (inl (true , a , b))
  f (inr b) (inl a) = inr (inl (false , (a , b)))
  f (inr b) (inr b₁) = inr (inr λ where
      true -> b
      false → b₁)
snd iso1 (inl a) b = inl (a b)
snd iso1 (inr (inl (false , a))) false = inl (fst a)
snd iso1 (inr (inl (true , a))) false = inr (snd a)
snd iso1 (inr (inl (false , a))) true = inr (snd a)
snd iso1 (inr (inl (true , a))) true = inl (fst a)
snd iso1 (inr (inr y)) b = inr (y b)

iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
fst iso2 f = (λ x → f (inl x)) , λ x → f (inr x)
snd iso2 (fs , _) (inl a) = fs a
snd iso2 (_ , sn) (inr b) = sn b

iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ Bool ⊎ ⊤
fst iso3 (inl a) = inl true
fst iso3 (inr (inl a)) = inl false
fst iso3 (inr (inr b)) = inr b
snd iso3 (inl false) = inr (inl tt)
snd iso3 (inl true) = inl tt
snd iso3 (inr b) = inr (inr b)
testiso3 : fst iso3 (inl tt) ≡ fst iso3 (inr (inl tt)) → ⊥
testiso3 ()
testiso3' : fst iso3 (inl tt) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3'' ()

iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ (⊤ ⊎ ⊤)
fst iso4 x = f (x tt) where
   f : ⊤ ⊎ ⊥ ⊎ ⊤ →  ⊤ ⊎ ⊤
   f (inl a) = inl a
   f (inr (inr b)) = inr b
snd iso4 (inl a) x₁ = inl a
snd iso4 (inr b) x₁ = inr (inr b)
testiso4 : fst iso4 (λ _ → inl tt) ≡ fst iso4 (λ _ → inr (inr tt)) → ⊥
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≡ snd iso4 (inr tt) tt → ⊥
testiso4' ()

```
