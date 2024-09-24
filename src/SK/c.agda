{-# OPTIONS --rewriting #-}

open import SK.php

module SK.c where

infix 3 _≡_
infixl 6 _◾_
infixl 2 _⊎_
-- infixl 4 ¬_
infixl 4 _·'_

data _≡_ {i}{A : Set i}(a : A) : A → Set i where
  refl : a ≡ a

{-# BUILTIN REWRITE _≡_ #-}

data Bool : Set where true false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
  
data Fin : ℕ → Set where  
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)


  
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B 

data Σ (A : Set)(B : A → Set) : Set where
  _,_  : (a : A) → B a → Σ A B 

record ⊤ : Set where constructor tt
data ⊥ : Set where

-- data _—→_ : Model.Tm → Model.Tm → Set where

-- ¬_ : Set → Set
-- ¬ A = A → ⊥

exfalso : ∀{ℓ}{A : Set ℓ} → ⊥ → A
exfalso ()

_◾_ : ∀{i}{A : Set i}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ◾ refl = refl
cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl
sym : ∀{i}{A : Set i}{a b : A } → a ≡ b → b ≡ a
sym refl = refl
trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl  =  refl

data _⊎_ {i}(A B : Set i) : Set i where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
-- subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
-- subst P refl px = px


module Syn where
  infixl 4 _·_
  postulate
    Tm  : Set
    _·_ : Tm → Tm → Tm
    K S : Tm
    Kβ  : ∀{u f} → K · u · f ≡ u
    Sβ  : ∀{f g u} → S · f · g · u ≡ f · u · (g · u)

data NF : Set where
  K₀ : NF
  K₁ : NF → NF
  S₀ : NF
  S₁ : NF → NF
  S₂ : NF → NF → NF

-- combinatory algebra, model of combinator calculus/logic
record Model : Set₁ where
  infixl 4 _·_
  field
    Tm  : Set
    _·_ : Tm → Tm → Tm
    K S : Tm
    Kβ  : ∀{u f} → K · u · f ≡ u
    Sβ  : ∀{f g u} → S · f · g · u ≡ f · u · (g · u)
  postulate
    ⟦_⟧ : Syn.Tm → Tm
    ⟦·⟧ : ∀{t u} →  ⟦ t Syn.· u ⟧ ≡  ⟦ t ⟧ ·  ⟦ u ⟧
    ⟦K⟧ : ⟦ Syn.K ⟧ ≡ K
    ⟦S⟧ : ⟦ Syn.S ⟧ ≡ S
  {-# REWRITE ⟦·⟧ ⟦K⟧ ⟦S⟧ #-}


-- ⟦_⟧ : Syn.Tm → M.Tm
-- ⟦ Syn.K ⟧ = M.K
-- ⟦ Syn.S ⟧ = M.S
-- ⟦ u Syn.· v ⟧ = ⟦ u ⟧ M· ⟦ v ⟧

data Tm' :  ℕ → Set where
  var : {n : ℕ} → Fin n → Tm' n
  lam : {n : ℕ} → Tm' (suc n) → Tm' n
  _·'_ : {n : ℕ} → Tm' n → Tm' n → Tm' n 


idTm' : Tm' (suc zero)
idTm' = lam (var fzero)

data Tm'' :  ℕ → Set where
  var : {n : ℕ} → Fin n → Tm'' n
  _·'_ : {n : ℕ} → Tm'' n → Tm'' n → Tm'' n 
  K' : {n : ℕ} →  Tm'' n
  S' : {n : ℕ} →  Tm'' n
  
lam* : {n : ℕ} → Tm'' (suc n) → Tm'' n 
lam* (var fzero) = S' ·' K' ·' K' 
lam* (var (fsuc x)) = K' ·' var x
lam* K' = K' ·' K'
lam* S' = K' ·' S'
lam* (t ·' u) = S' ·' lam* t ·' lam* u

conv :  {n : ℕ} →  Tm' n → Tm'' n
conv (var i) = var i
conv (t ·' u) = conv t ·' conv u
conv (lam t) = lam* (conv t)

idTm'' : Tm'' (suc zero)
idTm'' = conv idTm'
-- S' ·' K' ·' K'

kTm' : Tm' (suc (suc zero))
kTm' = lam (lam ((var (fsuc fzero) ) ·' (var (fzero))))
--fsuc 
kTm'' : Tm'' (suc(suc zero))
kTm'' = conv kTm'

abcTm' : Tm' (suc (suc zero))
abcTm' = lam (lam (lam (var (fsuc (fsuc fzero)) ·' var (fsuc fzero) ·' var (fzero))))

abcTm'' : Tm'' (suc (suc zero))
abcTm'' = conv abcTm'
-- idTm'' = conv idTm'
-- S' ·' (K' ·' K') ·' (S' ·' K' ·' K')

-- K · (K · K) ≠ (K · K) · K = K · K · K

module programmingWithCombinators (m : Model) where
  open Model m
   
  ⌜_⌝ : NF → Tm
  ⌜ K₀ ⌝ = K
  ⌜ K₁ x ⌝  = K · ⌜ x ⌝ 
  ⌜ S₀ ⌝ = S
  ⌜ S₁ x ⌝ = S ·  ⌜ x ⌝ 
  ⌜ S₂ x x₁ ⌝ = S ·  ⌜ x ⌝  ·  ⌜ x₁ ⌝ 

  {-# TERMINATING #-}
  app : NF → NF → NF
  app K₀ x = K₁ x
  app (K₁ x₁) x = x₁
  app S₀ x = S₁ x
  app (S₁ x₁) x = S₂ x₁ x
  app (S₂ x₁ x₂) x = app (app x₁ x) (app x₂ x) 

  Mod : Model
  Mod = record { Tm = NF ; _·_ = app ; K = K₀ ; S = S₀ ; Kβ = refl ; Sβ = refl }
  module Mod = Model Mod

  appβ : ∀{n n'} → app (app K₀ n) n' ≡ app (K₁ n) n'
  appβ {n}{n'} = refl

  kTm : Tm 
  kTm = S · (K · K) · (S · K · K)
  kTmβ : ∀ {x y} → kTm · x · y ≡ x 
  kTmβ {x} {y} = 
    cong (λ z → z · y) Sβ ◾
    cong (λ z → z · (S · K · K · x) · y) Kβ ◾
    cong (λ z → z ) Kβ ◾
    cong (λ z → z ) Sβ ◾
    Kβ
  -- EXE: easy
  -- three components, like K · K · K
  I : Tm
  I = S · K · K
  Iβ : ∀{u} → I · u ≡ u
  Iβ {u} =
    Sβ ◾
    Kβ 
  
  B : Tm
  B = S · (K · S) · K
  Bβ : ∀{f g u} → B · f · g · u ≡ f · (g · u)
  Bβ {f}{g}{u} = 
    cong (λ z → z · g · u) Sβ ◾
    cong (λ z → z · (K · f) · g · u) Kβ ◾
    Sβ ◾
    cong (λ z → z · (g · u)) Kβ


  C : Tm
  C = S · (S · (K · B) · S) · (K · K)
  Cβ : ∀{f g u} → C · f · u · g ≡ f · g · u
  Cβ {f}{g}{u} = 
    cong (λ z → z · u · g) Sβ ◾
    cong (λ z → z · ((K · K) · f) · u · g) Sβ ◾
    cong (λ z → z · (S · f) · ((K · K) · f) · u · g) Kβ ◾
    cong (λ z → z · ((K · K) · f) · u · g ) Sβ ◾
    cong (λ z → z · (K · (S · f)) · ((K · K) · f) · u · g) Kβ ◾
    cong (λ z → z · g) Sβ ◾
    cong (λ z → z · (((K · K) · f) · u) · g ) Kβ ◾
    cong (λ z → (S · f) · (z · u) · g )  Kβ ◾
    Sβ ◾
    cong (λ z → (f · g) · z) Kβ
  
  zero' : Tm
  zero' = K
  zeroβ : ∀{z s} → zero' · z · s ≡ z
  zeroβ = Kβ

  one : Tm
  one = C · I  -- S · (S · (K · (S · (K · S) · K)) · S) · (K · K) · I
  oneβ : ∀{z s} → one · z · s ≡ s · z
  oneβ {z}{s} = Cβ ◾
    cong (λ x → x · z) Iβ

  two : Tm
  two =  B · (S · I) · one
  twoβ : ∀{z s} → two · z · s ≡ s · (s · z)
  twoβ {z}{s} = 
    cong (λ x → x · s ) Bβ ◾
    Sβ ◾
    cong (λ x → I · s · x ) oneβ ◾
    cong (λ x → x  · (s · z)) Iβ
    
  three : Tm
  three =  B · (S · I) · two
  threeβ : ∀{z s} → three · z · s ≡ s · (s · (s · z))
  threeβ {z}{s} = 
    cong (λ x → x · s ) Bβ ◾
    Sβ ◾
    cong (λ x → I · s · x ) twoβ ◾
    cong (λ x → x  · (s · (s · z))) Iβ

  -- EXE: easy
  succ : Tm
  succ =  B · (S · I)
  sucβ : ∀{n z s} → succ · n · z · s ≡ s · (n · z · s) -- \n f x -> f(n f x)
  sucβ {n}{z}{s}= 
    cong  (λ x → x · s ) Bβ ◾
    Sβ ◾
    cong (λ x → x  · (n · z · s) ) Iβ

  suctwo : ∀{z s} → succ · two · z · s ≡ three · z · s
  suctwo {z}{s}= 
    cong (λ x → x) sucβ ◾
    cong (λ x → s · x ) twoβ ◾
    cong (λ x → x) (sym threeβ)
    
  -- pred: \n f x -> n(\g h -> h (g f)) (\u -> x) (\u ->u)

  -- B(B(R I))(B(R K)(B(B B)(R(B(B T) T) B)))

  -- \n x f -> n (\u -> x) (\g h -> h (g f)) (\u ->u)
  -- B(B(R I))
  -- (B(R(B(B T) T))(B(B B)(R K B)))
-- EXE: easy
  R : Tm
  R = B · B · one
  Rβ : ∀{n z s} → R · n · z · s ≡ z · s · n
  Rβ {n}{z}{s}= 
    cong (λ x → x · z · s) Bβ ◾
    cong (λ x → x) Bβ ◾
    cong (λ x → x) oneβ 
  
  pred : Tm
  pred = B ·  (B · (R  · I)) · (B · (R · (B · (B  · one)  · one)) · (B · (B ·  B) · (R ·  K  · B)))

  predβ : ∀ {s z} → pred · (two) · z · s ≡  one · z · s
  predβ {s}{z} = 
    cong  (λ x → x · z · s) Bβ ◾
    cong (λ x → x · s) Bβ ◾
    cong  (λ x → x ) Rβ ◾
    cong (λ x → x · z · s · I) Bβ ◾
    cong (λ x → x  · s · I) Rβ ◾
    cong (λ x → x · z · (B · (B · one) · one) · s · I) Bβ ◾
    cong (λ x → x · (B · (B · one) · one) · s · I) Bβ ◾
    cong (λ x → x · I) Bβ ◾
    cong  (λ x → x · z · (B · (B · one) · one · s) · I ) Rβ ◾
    cong (λ x → x · (B · (B · one) · one · s) · I ) Bβ ◾
    cong (λ x → x ·  I) twoβ ◾
    cong (λ x → x ·  (B · (B · one) · one · s · (K · z)) · I)  Bβ ◾
    cong  (λ x → x ·  I) Bβ ◾
    cong (λ x → x ) oneβ ◾
    cong (λ x → x ) Iβ ◾
    cong (λ x → x ) oneβ ◾
    cong (λ x → x ·  (K · z) · s) Bβ ◾
    cong (λ x → x ·  s) Bβ ◾
    cong (λ x → x ) oneβ ◾
    cong (λ x → s · x ) oneβ ◾
    cong (λ x → s · x ) Kβ ◾
    cong (λ x →  x ) (sym oneβ) 
 
  predβ' : ∀ {z s} → pred ·  zero' · z · s ≡ z
  predβ' {z}{s}= 
    cong  (λ x → x · z · s) Bβ ◾
    cong (λ x → x · s) Bβ ◾
    cong  (λ x → x ) Rβ ◾
    cong (λ x → x · z · s · I) Bβ ◾
    cong (λ x → x  · s · I) Rβ ◾
    cong (λ x → x · z · (B · (B · one) · one) · s · I) Bβ ◾
    cong (λ x → x · (B · (B · one) · one) · s · I) Bβ ◾
    cong (λ x → x · I) Bβ ◾
    cong  (λ x → x · z · (B · (B · one) · one · s) · I ) Rβ ◾
    cong (λ x → x · (B · (B · one) · one · s) · I ) Bβ ◾
    cong (λ x → x · I ) zeroβ ◾
    Kβ
  
   
  add : Tm
  add = B · (B · (R · I)) · (B · (B · (B · S)) · (B · B · B))
  addβ : ∀{a b z s} → add · a · b · z · s ≡ a · (b · z · s) · s
  addβ {a}{b}{z}{s}= 
    cong (λ x → x · b · z · s) Bβ  ◾
    cong (λ x → x · z · s) Bβ  ◾
    cong (λ x → x · s) Rβ  ◾
    cong (λ x → x · b · z · I · s) Bβ  ◾
    cong (λ x → x · z · I · s) Bβ  ◾
    cong (λ x → x · I · s) Bβ  ◾
    cong (λ x → x) Sβ  ◾
    cong (λ x → x · b · z · s · (I · s)) Bβ  ◾
    cong (λ x → x · s · (I · s)) Bβ  ◾
    cong (λ x → x ·(I · s)) Bβ  ◾
    cong (λ x → a · (b · z · s) · x) Iβ 
    
  addβ' : ∀{b z s} → add · zero' · b · z · s ≡ b · z · s
  addβ' {b}{z}{s}=
    cong (λ x → x) addβ  ◾
    cong  (λ x → x) zeroβ 

  addβ'' : ∀{a b z s} → add · (succ · a) · b · z · s ≡ succ · (add · a · b) · z · s
  addβ'' {a}{b}{z}{s}=
    cong (λ x → x) addβ  ◾
    cong (λ x → x) sucβ  ◾
    cong  (λ x → s · x)  (sym addβ)  ◾
    cong (λ x → x) (sym sucβ )

  -- EXE: easy
  mul : Tm
  mul = R · C · (B ·  B · (B ·  C · (B · B))) -- \a b z s . a z (\x. b x s)
  mulβ' : ∀{b z s} → mul · zero' · b · z · s ≡ zero' · z · s
  mulβ' {b}{z}{s}= 
    cong (λ x → x · b · z · s ) Rβ   ◾
    cong (λ x → x · C · b · z · s) Bβ   ◾
    cong (λ x → x · z · s) Bβ   ◾
    cong (λ x → x · (C · b) · z · s )  Bβ   ◾
    cong (λ x → x · s) Cβ   ◾
    cong (λ x → x · (C · b) · s) Bβ   ◾
    cong (λ x → x) Bβ   ◾
    cong (λ x → x) zeroβ   ◾
    cong (λ x → x) (sym zeroβ )
 
  eq? :  ∀{a b z s} → (R · C · (B ·  B · (B ·  C · (B · B)))) · a · b · z · s ≡ a · z · (C · b · s)
  eq? {a}{b}{z}{s} = 
    cong (λ x → x · b ·  z · s) Rβ ◾
    cong (λ x → x · C · b · z · s) Bβ ◾
    cong (λ x → x · z · s) Bβ ◾
    cong (λ x → x · (C · b) · z · s) Bβ ◾
    cong (λ x → x  · s) Cβ ◾
    cong (λ x → x · (C · b) · s) Bβ ◾
    Bβ 

  eq1 : ∀{a b z s} →  add · b · (mul · a · b) · z · s ≡ (b · (a · z · (C · b · s)) · s)
  eq1  {a}{b}{z}{s} = 
    cong (λ x → x  ) addβ ◾
    cong  (λ x → b · x · s) eq? 

  mulβ'' : ∀{a b z s} → mul · ( B · (S · I) · a) · b · z · s ≡ add · b · (mul · a · b) · z · s
  mulβ'' {a}{b}{z}{s}= 
    cong (λ x → x · b · z · s ) Rβ   ◾
    cong (λ x → x · C · b · z · s) Bβ   ◾
    cong (λ x → B · x · C · b · z · s) Bβ  ◾
    cong (λ x → x · z · s) Bβ   ◾
    cong (λ x → x · s) Cβ   ◾
    cong (λ x → x · (C · b) · s) Bβ   ◾
    cong (λ x → x ) Bβ   ◾
    cong (λ x → x · (C · b · s)) Bβ   ◾
    cong (λ x → x ) Sβ   ◾
    cong (λ x → x · (a · z · (C · b · s))) Iβ   ◾
    cong (λ x → x ) Cβ   ◾
    cong (λ x → x ) (sym eq1)
 
  M : Tm
  M = S · I · I
  Mβ : ∀{f} → M · f ≡ f · f
  Mβ {f}=
    Sβ ◾
    cong (λ z → z · z) Iβ

  L : Tm
  L = C · B · M
  Lβ : ∀{f g} → L · f · g ≡ f · ( g · g )
  Lβ {f}{g}=
    cong (λ z → z · g) Cβ ◾
    Bβ ◾
    cong (λ z → f · z) Mβ

  --· ( S · L · L · f)
  -- x is a fixpoint of f if "f · x = x"
    -- in lambda calculus: λf.(λx.f(x x))(λx.f(x x))
  -- EXE: bit harder
  Y : Tm
  Y = S · L · L
  Yβ : ∀{f} → Y · f ≡ f · (Y · f)
  Yβ {f}=
    Sβ ◾
    Lβ ◾ 
    cong (λ z → f · z) (sym Sβ)

  -- EXE: bit harder
  -- implement suc, add, mul using Y
  -- with fixpoint combinator, any recursive function can be defined
  -- addy : Tm
  -- addy = Y · add

  true' : Tm
  true' = K 
  trueβ' : ∀{x y} → true' · x · y ≡ x
  trueβ' = Kβ
   

  false' : Tm
  false' = S · K
  falseβ' : ∀{x y} → false' · x · y ≡ y
  falseβ' {x}{y} =  
    cong (λ z → z ) Sβ  ◾
    Kβ

  -- if : Tm
  -- if  = {!   !}
  -- iftβ : ∀{b t f} → if · true' · t · f ≡ t
  -- iftβ = {!   !}

  -- iffβ : ∀{b t f} → if · false' · t · f ≡ f
  -- iffβ = {!   !}
    
  
  iszero : Tm
  iszero = R · (K  · false') · ((C · I) · true')
  -- iszeroβ :\n -> n true (\x -> false) = R(K false)(T true)

  iszeroβ' :  iszero · zero' ≡ true' --K₁ (K₁ (S₂ K₀ K₀))
  iszeroβ' = 
    cong (λ z → z ) Rβ  ◾
    cong (λ z → z ·  (K · false') ) Cβ  ◾
    cong (λ i → i · true' · (K · false') ) Iβ  ◾
    zeroβ
    
  iszeroβ'' : ∀ {n} → iszero · (succ · n) ≡ false' 
  iszeroβ'' = 
    cong (λ z → z ) Rβ  ◾
    cong (λ z → z ·  (K · false') ) Cβ  ◾
    cong (λ i → i · true' · (K · false') ) Iβ  ◾
    cong (λ z → z ) sucβ  ◾
    Kβ

  addy :  ∀{f a b} → (iszero · a) · b ·  (succ ·  (f · (pred · a) · b)) ≡ {!   !}
  addy =   {!   !}


  fact : Tm
  fact = {!  (iszero · a) · b ·  (succ ·  (f · (pred · a) · b)) !}
  factβ : {!   !}
  factβ = {!   !}
    
  -- addr : ∀{n b} → add · n · b ≡ Y · addy · n · b 
  -- addr = {!   !}

Syn : Model
Syn = record { Tm = Syn.Tm ; _·_ = Syn._·_ ; K = Syn.K ; S = Syn.S ; Kβ = Syn.Kβ ; Sβ = Syn.Sβ }

module test where
  open programmingWithCombinators Syn
  open Syn
  -- what is the normal form of I · I?
  nfII : Mod.⟦ I · I ⟧ ≡ S₂ K₀ K₀
  nfII  = refl

  a = {!  Mod.⟦ S · (K · (S · (K · (one · I)))) · (S · (K · (one · (S · (K · (S · (K · one))) · one))) · (S · (K · B) · (S · (K · zero') · K)))  ⟧  !}

  -- suc : Tm
  -- suc =  B · (S · I)
  -- sucβ : ∀{n z s} → suc · n · z · s ≡ s · (n · z · s)
  -- -- \n f x -> f(n f x)
  -- sucβ {n}{z}{s}= 
  --   cong  (λ x → x · s ) Bβ ◾
  --   Sβ ◾
  --   cong (λ x → x  · (n · z · s) ) Iβ
  
-- EXE:
inequality : (m : Model) → let open Model m in K · (K · K) ≡ (K · K) · K → K ≡ S
inequality = {!!}

trivialModel : (m : Model) → let open Model m in K ≡ S → (a b : Tm) → a ≡ b
trivialModel record { Tm = Tm ; _·_ = _·_ ; K = K ; S = .K ; Kβ = Kβ ; Sβ = Sβ } refl a b = {!   !}

Kβ' : ∀ {u f : Bool} → f ≡ u
Kβ' {true} {true} = refl
Kβ' {false} {false} = refl
Kβ' {true} {false} = {!   !}
Kβ' {false} {true} =  {!   !}

-- there is a trivial model

trivial : Model
trivial = record { Tm = ⊤ ; _·_ = λ _ _ → tt ; K = tt ; S = tt ; Kβ =  refl ; Sβ = refl }

-- there is no such model:
-- is there a model with 2 elements?
b : Model
b = record { Tm = Bool ; _·_ = λ Bool Bool → Bool; K = true ; S = false ; Kβ =  λ {u f} → Kβ' ; Sβ = refl }


module notBoolModel

  (_·_ : Bool → Bool → Bool)
  (K S : Bool)
  (Kβ  : ∀{u f} → (K · u) · f ≡ u)
  (Sβ  : ∀{f g u} → ((S · f) · g) · u ≡ (f · u) · (g · u))
  
  where

  Tm = Bool
  B : Tm
  B = (S · (K · S)) · K
  Bβ' : ∀{f g u} → ((B · f) · g ) · u ≡ f · (g · u)
  Bβ' {f}{g}{u} = 
    cong (λ z → (z · g) · u) Sβ ◾
    cong (λ z → ((z · (K · f)) · g) · u) Kβ ◾
    Sβ ◾
    cong (λ z → z · (g · u)) Kβ

  I : Tm
  I = (S · K) · K
  Iβ : ∀{u} → I · u ≡ u
  Iβ {u} =
    Sβ ◾
    Kβ 

  fst : Tm  -- proj 0
  fst = (B · K) · K
  fstβ : ∀ {a b c} → ((fst · a) · b) · c ≡ a
  fstβ {a}{b}{c} =
    cong  (λ z → (z · b) · c) Bβ' ◾
    cong  (λ z → z · c) Kβ ◾
    Kβ
  snd : Tm -- proj 1
  snd = K · K
  thd : Tm -- proj 2
  thd = K · (K · I)
  sndβ : ∀ {a b c} → ((snd · a) · b) · c ≡ b
  sndβ {a}{b}{c} =
    cong  (λ z → (z · b) · c) Kβ ◾
    Kβ
  thdβ : ∀ {a b c} → ((thd · a) · b) · c  ≡ c
  thdβ {a}{b}{c} =
    cong  (λ z → (z · b) · c) Kβ ◾
    cong  (λ z → z · c) Kβ ◾
    Iβ
    
  pigeonHoleBool : (a b c : Tm) → a ≡ b ⊎ a ≡ c ⊎ b ≡ c
  pigeonHoleBool true true true = inl (inl refl)   -- All true
  pigeonHoleBool false false false = inl (inl refl) -- All false
  pigeonHoleBool true true false = inl (inl refl)  -- a ≡ b
  pigeonHoleBool true false true = inl (inr refl)  -- a ≡ c
  pigeonHoleBool false false true = inl (inl refl) -- a ≡ b
  pigeonHoleBool false true false = inl (inr refl) -- a ≡ c
  pigeonHoleBool true false false = inr refl -- b ≡ c
  pigeonHoleBool false true true = inr refl


  case1 : fst ≡ snd → ((fst · true) · false) · false ≡ ((snd · true) · false) · false
  case1 = λ x → cong (λ f → ((f · true) · false) · false) x
  case1' : fst ≡ snd → true ≡ false
  case1' x = trans (sym fstβ)   (trans (case1 x) sndβ)

  case2 : fst ≡ thd → ((fst · true) · false) · false ≡ ((thd · true) · false) · false
  case2 = λ x → cong (λ f → ((f · true) · false) · false) x
  case2' : fst ≡ thd → true ≡ false
  case2'  x = trans (sym fstβ) (trans (case2 x) thdβ )

  case3 : snd ≡ thd → ((snd · false) · true) · false ≡ ((thd · false) · true) · false
  case3 =   λ x → cong (λ f → ((f · false) · true) · false) x
  case3' : snd ≡ thd → true ≡ false
  case3' x =  trans (sym sndβ) (trans (case3 x) thdβ)

  fromPigeon : fst ≡ snd ⊎ fst ≡ thd ⊎ snd ≡ thd
  fromPigeon  = pigeonHoleBool fst snd thd
  
  -- combining fromPigeon and case1', case2', case3'
  contra : true ≡ false
  contra with fromPigeon
  contra | inl (inl x) = case1' x
  contra | inl (inr x) = case2' x
  contra | inr x = case3' x
  
  bot : ⊥
  bot with contra
  bot | ()
  

-- EXE: not hard
-- there is no model with two elements
notbool : (m : Model) → let module m = Model m in m.Tm ≡ Bool → ⊥
notbool m refl = notBoolModel.bot _·_ K S Kβ Sβ
  where
    open Model m

-- EXE: hard
-- is there a model with finitely many elements?
f : Model
f = record { Tm = {!   !} ; _·_ = {!   !} ; K = {!   !} ; S = {!   !} ; Kβ = {!   !} ; Sβ = {!   !} }

module notFiniteModel
  (n : ℕ)
  (_·_ : ∀ {n} → Fin n → Fin n → Fin n)
  (K S : ∀ {n} → Fin n)
  (Kβ : ∀ {n} {u f : Fin n} → (K {n} · u) · f ≡ u)
  (Sβ : ∀ {n} {f g u : Fin n} → ((S {n} · f) · g) · u ≡ (f · u) · (g · u))
 
  where
  
  B : ∀ {n} → Fin n
  B = (S · (K · S)) · K
  Bβ' : ∀ {n}{f g u} → ((B {n} · f) · g ) · u ≡ f · (g · u)
  Bβ' {n}{f}{g}{u} = 
    cong (λ z → (z · g) · u) Sβ ◾
    cong (λ z → ((z · (K · f)) · g) · u) Kβ ◾
    Sβ ◾
    cong (λ z → z · (g · u)) Kβ

  I :  ∀ {n} → Fin n
  I = (S · K) · K
  Iβ : ∀{n}{u} → I {n} · u ≡ u
  Iβ {n}{u} =
    Sβ ◾
    Kβ 
  
  C :  ∀ {n} → Fin n
  C = (S · ((S · (K · B)) · S)) · (K · K)
  Cβ : ∀{n}{f g u} → (((C {n} · f) · u) · g) ≡ (f · g) · u
  Cβ {n}{f}{g}{u} = 
    cong (λ z → (z · u) · g) Sβ ◾
    cong (λ z → ((z · ((K · K) · f)) · u) · g) Sβ ◾
    cong (λ z → (((z · (S · f)) · ((K · K) · f)) · u) · g) Kβ ◾
    cong (λ z → ((z · ((K · K) · f)) · u) · g ) Sβ ◾
    cong (λ z → (((z · (K · (S · f))) · ((K · K) · f)) · u) · g) Kβ ◾
    cong (λ z → z · g) Sβ ◾
    cong (λ z → (z · (((K · K) · f) · u)) · g ) Kβ ◾
    cong (λ z → ((S · f) · (z · u)) · g )  Kβ ◾
    Sβ ◾
    cong (λ z → (f · g) · z) Kβ

  zero' : ∀ {n} → Fin n
  zero' = K
  zeroβ : ∀{n}{z s} → (zero' {n} · z) · s ≡ z
  zeroβ {n} = Kβ
  
  -- EXE: easy
  one : ∀ {n} → Fin n
  one = C · I
  --S · (S · (K · (S · (K · S) · K)) · S) · (K · K) · I
  
  oneβ : ∀{n}{z s} → (one {n} · z) · s ≡ s · z
  oneβ {n}{z}{s} = Cβ ◾
    cong (λ x → x · z) Iβ
  


  
  
  fromfinitePigeon : {!   !}
  fromfinitePigeon  = {!   !}


notfinite : {n : ℕ } → (m : Model) → let module m =  Model m in m.Tm ≡ Fin n → ⊥
notfinite  = {!   !} --notBoolModel.bot _·_ K S Kβ Sβ


  -- 3 2 Syn.K Syn.· (Syn.K Syn.· (Syn.S Syn.· Syn.K Syn.· Syn.K))
  -- 4 0 Syn.S Syn.· (Syn.K Syn.· Syn.S) Syn.· Syn.K Syn.· Syn.K Syn.· Syn.K
  -- All β rule for S K 

-- pigeonhole : ∀ {m n} → m <ᵣ n → (f : Fin n → Fin m) →
--              ∃₂ λ i j → i ≢ j × f i ≡ f j

--   Pigeonholefinite' : ∀ {n : ℕ} → {j : Fin (suc n)}  → (xs : Vec (Fin n) (suc n)) → Σ (Fin (suc n)) λ x → xs !! x ≡ xs !! j
--   Pigeonholefinite' (x ∷ xs) = {!   !}

--   contra : true ≡ false
--   contra with fromPigeon
--   contra | inl (inl x) = case1' x
--   contra | inl (inr x) = case2' x
--   contra | inr x = case3' x
--   -- comnbining fromPigeon and case1', case2', case3'
--   bot : ⊥
--   bot with contra
--   bot | ()

--   where
--     open Model m


-- two : ∀ {n} → Fin n
--   two =  (B · (S · I)) · one
--   twoβ : ∀{n}{z s} → (two {n} · z) · s ≡ s · (s · z)
--   twoβ {n}{z}{s} = 
--     cong (λ x → x · s ) Bβ' ◾
--     Sβ ◾
--     cong (λ x → (I · s) · x ) oneβ ◾
--     cong (λ x → x  · (s · z)) Iβ
    
--   three : ∀ {n} → Fin n
--   three =  (B · (S · I)) · two
--   threeβ : ∀{n}{z s} → (three {n} · z) · s ≡ s · (s · (s · z))
--   threeβ {n}{z}{s} = 
--     cong (λ x → x · s ) Bβ' ◾
--     Sβ ◾
--     cong (λ x → (I · s) · x ) twoβ ◾
--     cong (λ x → x  · (s · (s · z))) Iβ


-- infixl 9 _!!_
-- _!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
-- _!!_ {A} {.(suc _)} (x ∷ xs) fzero = x
-- _!!_ {A} {.(suc _)} (x ∷ xs) (fsuc n₁) = xs !! n₁ 


    -- ⌞_⌟ :  (n : ℕ) → Fin (suc n)
    -- ⌞ zero ⌟ = fzero
    -- ⌞ suc n ⌟ = fsuc ⌞  n ⌟ --fsuc ⌞  n ⌟
    
          
  -- _·_ = _<>_

    -- Proj :  (n : ℕ)
    --         (_·_ :  Fin (suc n) → Fin (suc n) → Fin (suc n)) → let infixl 5 _·_; _·_ = _·_ in
    --         (K S :  Fin (suc n))
    --         (Kβ : {u f : Fin (suc n)} → K · u · f ≡ u)
    --         (Sβ :  {f g u : Fin (suc n)} → S · f · g · u ≡ (f · u) · (g · u)) → ℕ → Fin (suc n)
    -- Proj zero _·_ K S Kβ Sβ zero = let infixl 5 _·_; _·_ = _·_ in S · K · K
    -- Proj (suc zero) _·_ K S Kβ Sβ zero = K
    -- Proj (suc (suc n)) _·_ K S Kβ Sβ zero = let infixl 5 _·_; _·_ = _·_ in S · (K · S) · K · K · raiseᵣ 1 (Proj (suc n) {!   !} {!   !} {!   !} {!   !} {!   !} {!   !})
        
    -- Proj n _<>_ K S Kβ Sβ (suc i) = {!   !}
    
-- -- programmingWithCombinators.Proj Syn'

--   -- toℕ  
--   ⌜_⌝ : {n : ℕ} → Fin n → ℕ 
--   ⌜ fzero ⌝ = 0
--   ⌜ fsuc x ⌝ = suc  ⌜ x ⌝
--   -- fzero -> 0 fsuc fzero → 1 
--   Proj : (n : ℕ) → Fin n → Tm
--   Proj (suc zero) fzero = I -- (1,0) I
--   Proj (suc (suc zero)) fzero = K -- (2,0) K
--   Proj (suc (suc zero)) (fsuc fzero) = K · I -- (2,1) KI --from 2
--   Proj (suc (suc (suc n))) fzero = B · K ·  Proj (suc (suc n)) fzero -- the first line information,get the first element of every model
--   Proj (suc (suc (suc n))) (fsuc x) = K · Proj (suc (suc n))  x -- remove one B result -- the seconde line information

--   -- fromℕ 
--   ⌞_⌟ :  (n : ℕ) → Fin (suc n)
--   ⌞ zero ⌟ = fzero
--   ⌞ suc n ⌟ = fsuc ⌞  n ⌟
--   -- toℕ  
  
--   f : ∀ {n} → Fin n → Fin (suc n)
--   f fzero = fzero
--   f (fsuc x) = fsuc (f x)

--   -- programmingWithCombinators.test$
--   _$_ : Tm → {n : ℕ } → (Fin (suc n) → Tm) → Tm 
--   _$_ t {zero} w = t · w fzero
--   _$_ t {suc n} w = (_$_ t {n} λ j → w (lift-f 0 f j)) · w (fsuc ⌞  n ⌟)

--   KIβ : ∀ {a b} → K · I · a · b ≡ b
--   KIβ {a}{b} = 
--         cong  (λ z → z · b) Kβ ◾
--         Iβ  
        
--   BKβ : ∀ {a b c} → B · K · a · b · c ≡ a · b
--   BKβ {a}{b}{c} = 
--     cong  (λ z → z · c) Bβ ◾
--     Kβ

--   lower₁ : ∀ {n} → (w : Fin (suc n) → Tm) → (Fin n → Tm)
--   lower₁ {suc n} w x = w (lift-f 0 f x)
  
--   BKβ' : ∀ {a b c }{n : ℕ}{w : (Fin (suc n) → Tm)} → B · K · a $ w · b · c ≡ a $ w · b
--   BKβ' {a}{b}{c} = 
--     cong  (λ z → z · c)  Bβ ◾
--     Kβ

--   Projβ : ∀ {n} →  (i : Fin (suc n)) → (w : Fin (suc n) → Tm) → (Proj (suc n) i) $ w  ≡ w i 
--   Projβ {zero} fzero w = Iβ
--   Projβ {suc zero} fzero w = {!   !} --Kβ
--   Projβ {suc zero} (fsuc fzero) w = KIβ
--   Projβ {suc (suc n)} fzero w = trans {!     !} (Projβ fzero (lower₁ w)) --cong {! BKβ  !} {!   !} --{!   Projβ fzero (lower₁ w)!} -- Projβ fzero (lower₁  w  ) --Projβ {suc n} fzero w
--   Projβ {suc (suc n)} (fsuc i) w =  {!   !} --(Projβ {suc n} i (lower₁ λ x → w {!  x !}))


--   iteℕ : {A : Set} → A → (A → A) → ℕ → A 
--   iteℕ z s zero = {!   !}
--   iteℕ z s (suc n) = {!   !}

-- --  Tm → {n : ℕ } → (Fin (suc n) → Tm) → Tm 

--     -- cong  (λ z → z · c) Bβ ◾
--     -- Kβ
--    -- {!   !}

--   Proj'β : ∀ {n} →  (i : Fin n) → (w : Fin n → Tm) → (Proj  {!   !} {!   !} ) $ {!   !}  ≡ {!   !} {!   !} 
--   Proj'β = {!   !}
  

-- --   B · K · _a_1211 !=
-- -- Proj (suc (suc (suc n))) fzero $
-- -- (λ j → w (lift-f 0 f (lift-f 0 f j)))

--   -- the i-th term in w; $' w is all the terms in w.
--   fst₄ : Tm 
--   fst₄ = Proj 4 fzero
--   fst₄β : ∀ {a b c d} → fst₄ · a · b · c · d ≡ a
--   fst₄β {a}{b}{c}{d} =
--         cong  (λ z → (z · b) · c · d) Bβ ◾
--         cong  (λ z → z · c · d ) Kβ ◾
--         cong  (λ z → z · c · d) Bβ ◾
--         cong  (λ z → z · d ) Kβ ◾
--         Kβ
        
--   thd₄ : Tm 
--   thd₄ = Proj 4 (fsuc (fsuc fzero))
--   thd₄β : ∀ {a b c d} → thd₄ · a · b · c · d ≡ c
--   thd₄β {a}{b}{c}{d} =
--         cong   (λ z → (z · b) · c · d) Kβ ◾
--         cong   (λ z → z  · c · d) Kβ ◾
--         Kβ

--   snd₅ : Tm 
--   snd₅ = Proj 5  (fsuc fzero)
--   snd₅β : ∀ {a b c d e} → snd₅ · a · b · c · d · e ≡ b
--   snd₅β {a}{b}{c}{d}{e} = 
--          cong  (λ z → (z · b) · c · d · e) Kβ ◾
--          cong  (λ z → z · c · d · e) Bβ ◾
--          cong  (λ z → z   · d · e) Kβ ◾
--          cong  (λ z → z   · d · e) Bβ ◾
--          cong  (λ z → z  · e) Kβ ◾
--          Kβ

    -- map : {A B : Set}{n : ℕ}  → ( A → B) → Vec A n →  Vec B n
    -- map f [] = []
    -- map f (x ∷ xs) = (f x) ∷ (map f xs)

    -- maptoℕx : ∀ {m : ℕ} → Vec Tm (suc m) → Vec ℕ (suc m)
    -- maptoℕx = map ⌜_⌝

    -- mapto0x : ∀ {n : ℕ} → Vec ℕ n → Vec ℕ n
    -- mapto0x = map λ x → 0

    -- replace : ∀ {n : ℕ} → Vec ℕ n → Fin n → Vec ℕ n
    -- replace {n} (x ∷ u) fzero = 1 ∷ mapto0x u
    -- replace {n} (x ∷ u) (fsuc i) = 0 ∷ replace u i

    -- replace' : ∀ {n : ℕ} → Vec {!   !} n → Fin n → Vec {!   !} n
    -- replace' {n} (x ∷ u) f = {!   !}

    -- replacefin : ∀ {n : ℕ} → Vec Tm (suc n) → Fin (suc n) → Vec Tm (suc n)
    -- replacefin {n} (x ∷ x₂) fzero = lift-f 0 (proj (suc n)) fzero ∷ {!   !}
    -- replacefin {n} (x ∷ x₂) (fsuc x₁) = lift-f 0 (proj (suc n)) (fsuc {!  !}) ∷ {!   !}
    
-- module notBoolModel
--   (n : ℕ)
--   (_·_ :  Bool → Bool → Bool)
--   (let infixl 5 _·_; _·_ = _·_)
--   (K S :  Bool)
--   (Kβ : {u f : Bool} → (K · u) · f ≡ u)
--   (Sβ :  {f g u : Bool} → ((S · f) · g) · u ≡ (f · u) · (g · u))

--   where

--   Tm = Bool
--   infixl 5 _·s_
--   B : Tm
--   B = S · (K · S) · K
--   Bβ : ∀{f g u} → ((B · f) · g ) · u ≡ f · (g · u)
--   Bβ {f}{g}{u} = 
--     cong (λ z → (z · g) · u) Sβ ◾
--     cong (λ z → ((z · (K · f)) · g) · u) Kβ ◾
--     Sβ ◾
--     cong (λ z → z · (g · u)) Kβ

--   I : Tm
--   I = S · K · K
--   Iβ : ∀{u} → I · u ≡ u
--   Iβ {u} =
--     Sβ ◾
--     Kβ 

--   _·s_ : Tm → {n : ℕ} → Vec Tm n → Tm
--   _·s_ t {zero}  [] = t
--   _·s_ t {suc n} (u ∷ us)  = t · u ·s us

--   lookup : {A : Set }{n : ℕ} → Vec A n → Fin n → A
--   lookup (x ∷ xs) fzero    = x
--   lookup (x ∷ xs) (fsuc i) = lookup xs i
  
--   proj : (n : ℕ) → Fin n → Tm
--   proj (suc zero)    fzero    = I
--   proj (suc (suc n)) fzero    = B · K · proj (suc n) fzero
--   proj (suc (suc n)) (fsuc x) = K · proj (suc n) x

--   projβ : (n : ℕ)(x : Fin n)(us : Vec Tm n) → proj n x ·s us ≡ lookup us x
--   projβ (suc zero) fzero (x ∷ []) = Iβ
--   projβ (suc (suc n)) fzero (u ∷ u' ∷ us) = trans ((cong (λ z → z · u' ·s us) Bβ)) (trans (cong (λ z → z ·s us) Kβ) (projβ (suc n) fzero (u ∷ us))) -- trans (cong (λ z → z) Bβ) {!  (cong (λ z → z) Kβ) !} --trans (cong (λ z → z) Bβ) {!   !}
--   projβ (suc (suc n)) (fsuc x) (u ∷ u' ∷ us) = trans ((cong (λ x → x · u' ·s us) Kβ)) (projβ (suc n) x (u' ∷ us))

  -- fst : Tm  -- proj 0
  -- fst = (B · K) · K
  -- fstβ : ∀ {a b c} → ((fst · a) · b) · c ≡ a
  -- fstβ {a}{b}{c} =
  --   cong  (λ z → (z · b) · c) Bβ' ◾
  --   cong  (λ z → z · c) Kβ ◾
  --   Kβ
  -- snd : Tm -- proj 1
  -- snd = K · K
  -- thd : Tm -- proj 2
  -- thd = K · (K · I)
  -- sndβ : ∀ {a b c} → ((snd · a) · b) · c ≡ b
  -- sndβ {a}{b}{c} =
  --   cong  (λ z → (z · b) · c) Kβ ◾
  --   Kβ
  -- thdβ : ∀ {a b c} → ((thd · a) · b) · c  ≡ c
  -- thdβ {a}{b}{c} =
  --   cong  (λ z → (z · b) · c) Kβ ◾
  --   cong  (λ z → z · c) Kβ ◾
  --   Iβ
    
  -- pigeonhole : ∀ {m n} → m < n → (f : Fin n → Fin m) →
  --            ∃₂ λ i j → i ≢ j × f i ≡ f j 
  -- f : Fin 3 → Fin 2
  -- f fzero = {!((proj 3 fzero) ·  (fzero) · ( fsuc fzero ) ·  ( fsuc fzero ) )   !}
  -- f (fsuc x) = {!   !}
  -- fromPigeon' : (f : Fin 3 → Fin 2) → ∃₂ λ i j → i ≢ j × f i ≡ f j 
  -- fromPigeon' f = pigeonhole (s≤s (s≤s (s≤s z≤n))) f

  -- pigeonHoleBool : (a b c : Tm) → a ≡ b ⊎ a ≡ c ⊎ b ≡ c
  -- pigeonHoleBool false false c = inl refl
  -- pigeonHoleBool true true c = inl refl
  -- pigeonHoleBool false true false = inr (inl refl)
  -- pigeonHoleBool false true true = inr (inr refl)
  -- pigeonHoleBool true false false = inr (inr refl)
  -- pigeonHoleBool true false true = inr (inl refl)

  -- case1 : proj 3 fzero ≡ proj 3 (fsuc fzero) → ((proj 3 fzero) ·  true · false · false) ≡ (proj 3 (fsuc fzero)  ·  true · false · false)
  -- case1 = λ x → cong (λ f → f ·  true · false · false) x
  -- case1' : proj 3 fzero ≡ proj 3 (fsuc fzero) → true ≡ false
  -- case1' x = trans (sym (projβ 3 fzero (true ∷ (false ∷ (false ∷ []))))) (trans ( case1 x) (projβ 3 (fsuc fzero) (true ∷ (false ∷ (false ∷ []))))) 

  -- case2 : proj 3 fzero ≡  proj 3 (fsuc (fsuc fzero)) → ((proj 3 fzero · true) · false) · false ≡ ((proj 3 (fsuc (fsuc fzero)) · true) · false) · false
  -- case2 = λ x → cong (λ f → ((f · true) · false) · false) x
  -- case2' : proj 3 fzero ≡ proj 3 (fsuc (fsuc fzero)) → true ≡ false
  -- case2'  x = trans (sym (projβ 3 fzero (true ∷ (false ∷ (false ∷ []))))) (trans (case2 x) ((projβ 3 (fsuc (fsuc fzero)) (true ∷ (false ∷ (false ∷ [])))))) 

  -- case3 : proj 3 (fsuc fzero) ≡ proj 3 (fsuc (fsuc fzero)) → (proj 3 (fsuc fzero)) · false · true · false ≡ (proj 3 (fsuc (fsuc fzero))) · false · true · false 
  -- case3 =   λ x → cong (λ f → ((f · false) · true) · false) x
  -- case3' :  proj 3 (fsuc fzero) ≡ proj 3 (fsuc (fsuc fzero)) → true ≡ false
  -- case3' x =  trans (sym (projβ 3 (fsuc fzero) (false ∷ (true ∷ (false ∷ []))))) (trans (case3 x) (projβ 3 (fsuc (fsuc fzero)) (false ∷ (true ∷ (false ∷ []))))) 

  -- fromPigeon : proj 3 fzero ≡ proj 3 (fsuc fzero) ⊎ proj 3 fzero ≡ proj 3 (fsuc (fsuc fzero)) ⊎ proj 3 (fsuc fzero) ≡ proj 3 (fsuc (fsuc fzero))
  -- fromPigeon  = pigeonHoleBool (proj 3 fzero) (proj 3 (fsuc fzero)) (proj 3 (fsuc (fsuc fzero)))
  
  -- contra : true ≡ false
  -- contra with fromPigeon
  -- ... | inl a = case1' a
  -- ... | inr (inl a) = case2' a
  -- ... | inr (inr b) = case3' b
  
  -- bot : ⊥
  -- bot with contra
  -- bot | ()
 