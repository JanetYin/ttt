open import Lib hiding (_⊎_; case; _×_; _,_; tt)

{-
((λ x y → y) 3) =
((λ x → (λ y → y)) 3) =
(λ y → y)[x ↦ 3] =
(λ x → x)[x ↦ 3] =
(λ z → z)[x ↦ 3] =
(λ z → z)

-}

-- →, ℕ (0,1,2,3, _+_), Bool (true, false, if_then_else_)

b : Bool → Bool
b x = if x then false else true

data _⊎_ (A B : Set) : Set where -- osszeg, sum type, coproduct, diszjunkt unio (disjoint union)
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- A ⊎ B = Either A B
-- inj₁ = inl = Left = ι₁
-- inj₂ = inr = Right = ι₂

-- A : Set    B : Set
-- ------------------
--    A ⊎ B : Set

CustRef = ℕ
OrdNum  = ℕ

Id = CustRef ⊎ OrdNum

id1 id2 : Id
id1 = inj₁ 1200
id2 = inj₂ 1200

-- Bool ⊎ Bool = {inj₁ true , inj₁ false , inj₂ true , inj₂ true}
-- {true,false} ∪ {true,false} = {true,false}

case : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

-- A : Set    B : Set
-- ------------------
--    A × B : Set

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

-- A × B = (A,B) = tuple ami A-t es B-t tartalmaz = struct = ...
-- (1,true) :: (Int,Bool)
-- () :: ()
-- λ x → t : A → B

-- data tipus elemere mintat lehet illeszteni
-- record tipus elemet komintaillesztessel lehet letrehozni
{-
_,_ : {A B : Set} → A → B → A × B  -- record tipus β szabalyai
fst (a , b) = a
snd (a , b) = b

(a , b) = record { fst = a ; snd = b }

record η szabalya (surjective pairing)

w : A × B
-----------------
w = fst w , snd w

-}
-- A × B

-- Bool × ℕ   ≅   ℕ ⊎ ℕ     izomorizmus / bijekcio

-- α (true , 3) = inj₁ 3
-- α (true , 4) = inj₁ 4
-- α (false , 3) = inj₂ 3
α : Bool × ℕ → ℕ ⊎ ℕ
α w = if fst w then inj₁ (snd w) else inj₂ (snd w)

α⁻¹ : ℕ ⊎ ℕ → Bool × ℕ
α⁻¹ (inj₁ n) = true , n
α⁻¹ (inj₂ n) = false , n

-- α (α⁻¹ (inj₁ n)) = α (true , n) =
-- = if fst (true , n) then inj₁ (snd (true , n)) else inj₂ (snd (true , n))
-- = if true then inj₁ (snd (true , n)) else inj₂ (snd (true , n))
-- = inj₁ (snd (true , n))
-- = inj₁ n

-- Moses Schonfinkel
curry : {A B C : Set} → (A × B → C) → A → B → C
curry f a b = f (a , b)

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f ab = f (fst ab) (snd ab)

-- (A × B → C)  ≅  (A → B → C)

-- β : (λ x → t) u = t[x↦u]
-- η : f = (λ x → f x)
-- 2η : f = (λ x y → f x y)

{-
f : A → B → C
curry (λ ab → f (fst ab) (snd ab)) : A → (B → C)

       : A × B → C
       _________
      /         \
curry (uncurry f) =(η exp)
curry (λ ab → uncurry f ab) =(definicio)
curry (λ ab → f (fst ab) (snd ab)) =(η exp)
λ a → curry (λ ab → f (fst ab) (snd ab)) a =(η exp)
λ a b → curry (λ ab → f (fst ab) (snd ab)) a b =(η exp)
λ a b → (λ ab → f (fst ab) (snd ab)) (a , b) =(β)
λ a b → (f (fst ab) (snd ab))[ab ↦ (a , b)] =
λ a b → (f (fst (a , b)) (snd (a , b))) =(rovidites)
λ a b → (f a b) =
λ a → (λ b → f a b) =(η red)
λ a → f a =(η red)
f

f : A × B → C

uncurry (curry f) =(η)
λ ab → uncurry (curry f) ab =(rov)
λ ab → curry f (fst ab) (snd ab) =(rov)
λ ab → f (fst ab , snd ab) =(surj pairing)
λ ab → f ab =(η)
f
-}

-- ⊎ osszeg, × szorzat

-- a tipusok a ⊎-al felcsoportot alkotnak
-- alaphalmaz: Set, muvelet: ⊎, asszoc (egyenloseg: ≅)
assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C  →  A ⊎ (B ⊎ C)
assoc⊎ (inj₁ (inj₁ a)) = inj₁ a
assoc⊎ (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
assoc⊎ (inj₂ c) = inj₂ (inj₂ c)

-- visszafele is

-- egysegelem: A ⊎ 𝟘 ≅ A

data 𝟘 : Set where -- 𝟘, ⊥, empty type, ures tipus

case𝟘 : {C : Set} → 𝟘 → C
case𝟘 ()                   -- nincs minta, nincs eset, nincs konstruktor

egysegelem⊎ : {A : Set} → A ⊎ 𝟘 ↔ A
egysegelem⊎ = case (λ a → a) case𝟘 Lib., inj₁

-- Set a ⊎-al es 𝟘-val komm. egysegelemes felcsoportot alkotnak

-- A ⊎ B ≅ B ⊎ A

-- tipusok kommutativ felgyurut alkotnak

-- (A × B) × C ≅ A × (B × C)

record 𝟙 : Set where

tt : 𝟙
tt = record {}

-- 𝟙 × A ≅ A
-- 𝟘 × A ≅ 𝟘

-- a*(b+c) = a*b + a*c

-- 0,1,+,*,
-- a^(b+c) = a^b * a^c

hatv-szabaly : {A B C : Set} → (B → A) × (C → A) → ((B ⊎ C) → A)
hatv-szabaly = {!case!}

-- HF: (A ↔ B) → (B ↔ C) → (A ↔ C)

-- a^(b*c) = (a^b)^c

-- high school algebra: felgyuru exponencialis
