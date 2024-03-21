module gy06 where

open import Lib hiding (minMax)
import Lib.Containers.List as L
open L using (List; []; _∷_; length)
import Lib.Containers.Vector as V
open V using (Vec; []; _∷_)

---------------------------------------------------------
-- Sigma types
---------------------------------------------------------

-- Vissza a Vec-hez

fromList : {A : Set}(as : List A) → Vec A (length as)
fromList [] = []
fromList (x ∷ xs) = x ∷ fromList xs

-- ..., de függőtípusos rendezett párral.
{-
record Σ (A : Set)(B : A → Set) where
  fst : A
  snd : B fst
-}
-- \GS = Σ
what : Σ ℕ (Vec Bool)
what = 2 , true ∷ false ∷ []

filter : {A : Set}{n : ℕ}(p : A → Bool) → Vec A n → Σ ℕ (λ k → Vec A k) -- ezen lehet pontosítani, hiszen n elemnél nem kéne legyen benne több elem soha.
filter p [] = 0 , []
filter p (x ∷ xs) = let r@(k , ys) = filter p xs in if p x then (suc k , x ∷ ys) else r

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

length' : ∀{i}{A : Set i}{n : ℕ} → Vec A n → ℕ
length' _ = 0

smarterLengthVec : ∀{i}{A : Set i}{n} → Vec A n → Σ ℕ (λ k → n ≡ k)
smarterLengthVec {n = l} _ = l , refl

minMax' : ℕ → ℕ → ℕ × ℕ
minMax' n m = {!   !}

-- Ugyanez sokkal jobban, de leginkább pontosabban.
-- Az előző változatban vissza tudok adni csúnya dolgokat is.
-- Pl. konstans (0 , 0)-t.
minMax : (n m : ℕ) → {!!}
minMax n m = {!   !}

---------------------------------------------------------

Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
fst Σ=⊎ (false , ab) = inr ab
fst Σ=⊎ (true , ab) = inl ab
snd Σ=⊎ (inl a) = true , a
snd Σ=⊎ (inr b) = false , b

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
Σ=× = id , id

-- Π A F is essentially (a : A) → F a
-- what does this mean?

                    -- Π A (λ _ → B)
Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ↔ (A → B)
Π=→ = id , id

                    -- Π Bool (if_then A else B)
→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
fst →=× f = f true , f false
snd →=× (a , b) false = b
snd →=× (a , b) true = a

dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
fst dependentCurry f (a , b) = f a b
snd dependentCurry f a b = f (a , b)

------------------------------------------------------
-- Conat -- Pihenés
------------------------------------------------------

IsNotZero∞' : ℕ∞ → Set
IsNotZero∞' n with pred∞ n
... | just x = ⊤
... | nothing = ⊥

------------------------------------------------------
-- CoVec -- NEM lesz vizsgában, csak érdekesség most.
------------------------------------------------------

infixr 5 _∷_
record CoVec {ℓ}(A : Set ℓ) (n : ℕ∞) : Set ℓ where
  coinductive
  constructor _∷_
  field
    head : .⦃ IsNotZero∞ n ⦄ → A
    tail : .⦃ IsNotZero∞ n ⦄ → CoVec A (pred∞'' (pred∞ n))

open CoVec public
-- \{{ = ⦃
-- \}} = ⦄

[]' : ∀{i}{A : Set i} → CoVec A 0
head []' ⦃ () ⦄
tail []' ⦃ () ⦄

[1] : CoVec ℕ 1
[1] = 1 ∷ []'

replicate : ∀{i}{A : Set i}(n : ℕ∞) → A → CoVec A n
head (replicate n a) = a
tail (replicate n a) with pred∞ n
... | just x = replicate x a

repeat : ∀{i}{A : Set i} → A → CoVec A ∞
repeat a = replicate ∞ a

-- Nem nehéz, ugyanúgy megy, mint Stream-eknél.
map : ∀{i j}{A : Set i}{B : Set j}{n : ℕ∞} → {!!}
map = {!!}
