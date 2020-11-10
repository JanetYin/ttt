{-
példák további Bool bizonyításokra, pl. bal és jobb identitás és-re

pred kétféle változata
egyenlőség természetes számokra, tulajdonságai
-}

module lec.ea9 where

open import lib

pred pred' predPM pred'PM : ℕ → ℕ ⊎ ⊤

pred           = rec
                (inj₂ tt)
          (λ w → case w          (λ n → inj₁ (suc n)) (λ _ → inj₁ 0))
predPM zero    = inj₂ tt
predPM (suc n) = case (predPM n) (λ n → inj₁ (suc n)) (λ _ → inj₁ 0)

pred' = indℕ (λ _ → ℕ ⊎ ⊤)
                 (inj₂ tt)
         (λ n _ → inj₁ n)
pred'PM zero    = inj₂ tt
pred'PM (suc n) = inj₁ n

-- unit test
predtest1 : Eq _ (pred 100) (inj₁ 99)
predtest1 = refl
predtest2 : Eq _ (pred 0) (inj₂ _)
predtest2 = refl

pred'test1 : Eq _ (pred' 100) (inj₁ 99)
pred'test1 = refl

predtest3 : (n : ℕ) → Eq _ (pred (suc n)) (inj₁ n)
predtest3 = λ n → {!!}
-- nem igaz, hogy pred (suc n) = inj₁ n (definicio szerint)

pred'test3 : (n : ℕ) → Eq _ (pred' (suc n)) (inj₁ n)
pred'test3 = λ n → refl
-- pred' (suc n) = inj₁ n (definicio szerint)

eq0 : ℕ → Bool
eq0 = rec true (λ _ → false)

eqℕ : ℕ → ℕ → Bool
eqℕ = λ n → rec eq0 (λ eqn m → case (pred m) eqn (λ _ → false)) n

Eqℕ : ℕ → ℕ → Set
Eqℕ = λ a b → if eqℕ a b then ⊤ else ⊥

suc-inj : (a b : ℕ) → Eqℕ (suc a) (suc b) → Eqℕ a b
suc-inj = λ a b e → {!indℕ ...!}

{-
Eqℕ (suc a) (suc b) =
if eqℕ (suc a) (suc b) then ⊤ else ⊥ =
if rec eq0 (λ eqn m → case (pred' m) eqn (λ _ → false)) (suc a) (suc b) then ⊤ else ⊥ =
if case
    (pred' (suc b))
    (rec eq0 (λ eqn m → case (pred' m) eqn (λ _ → false)))
    (λ _ → false)
  then ⊤ else ⊥ =
if case
    (inj₁ b)
    (rec eq0 (λ eqn m → case (pred' m) eqn (λ _ → false)))
    (λ _ → false)
  then ⊤ else ⊥ =
if rec eq0 (λ eqn m → case (pred' m) eqn (λ _ → false)) b
  then ⊤ else ⊥ =
Eqℕ a b

pred és pred' ugyanúgy működik (matematikai szempontból), de pred'-vel
könnyebb programozni


------------------------------------

eddigi típusok: Bool, Nat, →,    ×, ⊎, ⊤, ⊥ <- jön a függő
Eqℕ, Eqb definiálható volt
VecBool is definiálható volt
VecBool : ℕ → Set
VecBool zero = ⊤
VecBool (suc n) = Bool × VecBool n

általános egyenlőség típus:

típusbevezető szabály:
  Eq : (A : Set) → A → A → Set
    Eq ℕ : ℕ → ℕ → Set               hasonló, mint az Eqℕ
    Eq Bool : Bool → Bool → Set      hasonló, mint az Eqb

konstruktor:
  refl : {A : Set}{a : A} → Eq A a a

eliminátor:
  transp : {A : Set}(P : A → Set){a a' : A} → Eq A a a' → P a → P a'

számítási szabály:
  transp {A} P {a}{a} refl u = u
-}

transp : {A : Set}(P : A → Set){a a' : A} → Eq A a a' → P a → P a'
transp {A} P {a}{a} refl u = u

{-
P x        →     P x'
  x        =      x'

Eq A a a   →     Eq A a' a
  a        =      a'

P x := Eq A x a          P x := Eq A x x

P a  = Eq A a a          P a  = Eq A a a
P a' = Eq A a' a         P a' = Eq A a' a'
-}
sym : {A : Set}{a a' : A} → Eq A a a' → Eq A a' a
sym' : {A : Set}{a a' : A} → Eq A a a' → Eq A a' a
sym  {A}{a}{a'} e    = transp (λ x → Eq A x a) e
                       refl
sym' {A}{a}{.a} refl = refl

{-
_×_ : Set → Set → Set        Σ : (A : Set) → (A → Set) → Set
_,_ : A → B → A × B          _,_ : (u : A) → B u → Σ A B
proj₁ : A × B → A            proj₁ : Σ A B → A
proj₂ : A × B → B            proj₂ : (w : Σ A B) → B (proj₁ w)
proj₁ (u , v) = u            proj₁ (u , v) = u
proj₂ (u , v) = v            proj₂ (u , v) = v

(1 , true) : ℕ × Bool       (1 , [true]) : Σ ℕ VecBool
                            (3 , [true,false,false]) : Σ ℕ VecBool
                            (2 , [true]) ez nem eleme Σ ℕ VecBool-nek

(x : Bool) → Eqb x (true ∨ x)        ∀x. x = true ∨ x
Σ Bool (λ x → Eqb x (false ∨ x))     ∃x. x = false ∨ x
-}
