module lec.ea7 where

open import lib

f : {X Y : Set} → X ⊎ Y → Y ⊎ X
f = λ w → case w inj₂ inj₁
{-
eddigi tipusok: →, ×, ⊎, ⊤, ⊥, ℕ, Bool

uj tipus: Set (univerzum, tipusok tipusa)
Bool : Set
zero : ℕ
ℕ    : Set
                (halmazeletben nem :, hanem ∈ van.  true ∈ 13)

_×_  : Set → Set → Set         <-  ha A tipus es B tipus, akkor A × B tipus
_×_ ℕ Bool = ℕ × Bool
_⊎_  : Set → Set → Set
-}

_^2 : Set → Set           -- ℕ ^2 = ℕ × ℕ
_^2 = λ A → A × A

-- A ^ 0 = ⊤
-- A ^ 1 = ⊤ × A
-- A ^ 2 = (⊤ × A) × A
-- A ^ 3 = ((⊤ × A) × A) × A
-- A ^ 4 = (((⊤ × A) × A) × A) × A
-- ...
_^_ : Set → ℕ → Set       
_^_ = λ A → λ n → rec ⊤ (λ B → B × A) n

-- ℕ ^ 30
fft ttf : Bool ^ 3
fft = ((_ , false) , false) , true
ttf = ((_ , true) , true) , false

-- Haskell
-- head : A ^ n → A ⊎ ⊤                List A → Maybe A        List A → Either () A
-- tail : A ^ 3 → A ^ 2                List A → List A

-- ¬ (X ^ 0 → X) = (X ^ 0 → X) → ⊥
--                 (⊤ ^ 0 → ⊤)
--                 (⊥ ^ 0 → ⊥) → ⊥
{-
leglényegesebb típus: függő → típus

A : Set      B : A → Set             ℕ : Set      (λ n → Bool ^ n) : ℕ → Set
------------------------             ---------------------------------------
  (x : A) → B x : Set                     (n : ℕ) → Bool ^ n : Set              függő típus

t : (n : ℕ) → Bool ^ n
t 3 : Bool ^ 3
t 4 : Bool ^ 4

Bool : Set      (λ b → if b then ℕ else Bool) : Bool → Set
----------------------------------------------------------
         (b : Bool) → if b then ℕ else Bool

t : (b : Bool) → if b then ℕ else Bool


ha t : B x, feltéve, hogy x : A               t : (x : A) → B x        u : A
-------------------------------bev            ------------------------------elim
  λ x → t : (x : A) → B x                             t u : B u

szam: (λ x → t) u = t[x↦u]        egyediseg: (λ x → t x) = t


A : Set      B : Set              A : Set           λ _ → B : A → Set
--------------------              -----------------------------------
    A → B : Set                           (_ : A) → B : Set

-}
t : (X : Set) → (X × ⊤ → X)
t = λ X → λ w → proj₁ w

-- implicit parameterek
t' : {X : Set} → (X × ⊤ → X)
t' = λ w → proj₁ w

-- ha implicit, es megis meg akarom nevezni, akkor {}-be irom
t'' : {X : Set} → (X × ⊤ → X)
t'' {X} w = proj₁ w

u : Bool × ⊤ → Bool
u = t Bool

u' : ℕ × ⊤ → ℕ
u' = t ℕ

u'' : ℕ
u'' = t ℕ (3 , tt)

v = t'' {ℕ → Bool × ℕ}

-- uj dolgok ma: Set, fuggo fuggveny tipus, implicit parameterek {}, = bal oldalan fuggveny beemenet
{-
zero : ℕ
true : Bool
ℕ : Set
Bool : Set
ℕ → Bool : Set
Set : Set₁ : Set₂ : Set₃ : ...
-}

-- w = t'' {Set → Bool}

open import Agda.Primitive

-- id : {i : _} → (A : Set i) → A → A            -- id :: a → a,     id :: forall a . a → a
-- id = λ A x → x

id : ∀{i}(A : Set i) → A → A        -- \forall
id = λ A x → x                      -- polimorf identitas fgv, nem csak Set-re mukodik, hanem
                                    -- Set₁-re, Set₂-re stb-re is

-- if_then_else_ : ∀{i}{A : Set i} → Bool → A → A → A

