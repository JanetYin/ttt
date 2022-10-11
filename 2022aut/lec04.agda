open import lib hiding (_+_; _*_; Bool; true; false; if_then_else_)

-- a = inl (inl (inr 3))

{-
(λ x → case x (λ x → true) (λ y → y)) (inj₂ false) = →β
(case x (λ x → true) (λ y → y))[x↦inj₂ false] = 
case (inj₂ false) (λ x → true) (λ y → y) = case def₂
(λ y → y) false = →β
y[y↦false] =
false

case (inj₁ (λ x → x)) (λ y → y true) (λ z → false) =
(λ y → y true) (λ x → x) =
(y true)[y ↦ (λ x → x)] =
(λ x → x) true =
x[x↦true]=
true

snd (1 , 3) = 3 = fst (3 , 1)

(λ x → (proj₁ x , proj₂ x)) = (λ x → x)                         x : A × B

-- 1 + proj₁ x = 1 + proj₁ (proj₁ x , proj₂ x)

(λ x → case x (λ y → true) (λ z → true))   : (_A ⊎ _B) → Bool

(λ x → true) : _A → Bool	

NixOS <- tisztan funkcionalis linux distro

if x then true else true = true

-}

-- unit teszt
e : (λ (x : ⊥ × ⊥) → x) ≡ (λ x → fst x , snd x)
e = refl

-- eddig: →, ×, ⊎, ⊥, ⊤       ⊤ ⊎ ⊤ =: Bool,     Nat,

-- poor man's bool

Bool = ⊤ ⊎ ⊤
true : Bool
true = inl tt  -- C-c C-r  refine   -- C-c C-a  autoa
false : Bool
false = inr tt
if_then_else_ : {A : Type} → Bool → A → A → A
if b then m else n = case b (λ _ → m) (λ _ → n)
-- if inl _ then m else n = m
-- if inr _ then m else n = n
{-
data ℕ : Type where -- induktiv, adattipus
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
-}

-- ℕ = {zero, suc zero, suc (suc zero), suc (suc (suc zero)), ...}
-- 0, 0', 0'', ...
-- unaris termeszetes szamok

ℤ = (ℕ ⊎ ⊤) ⊎ ℕ
nulla : ℤ
nulla = inl (inr tt)
neg_minus1 : ℕ → ℤ
neg n minus1 = inl (inl n)
minus1 : ℤ
minus1 = neg zero minus1
minus2 : ℤ
minus2 = neg suc zero minus1
minus3 : ℤ
minus3 = neg suc (suc zero) minus1

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))
{-
double 3 =
double (suc (suc (suc zero))) =
            \______________/
               n
suc (suc (double (suc (suc zero)))) =
                      \________/
                        n
suc (suc (suc (suc (double (suc zero))))) =
                                n
suc (suc (suc (suc (suc (suc (double zero)))))) =
suc (suc (suc (suc (suc (suc zero))))) = 6
-}

data Maybe (A : Type) : Type where
  Nothing : Maybe A
  Just    : A → Maybe A

-- Bool ≅ ⊤ ⊎ ⊤
-- Maybe A ≅ ⊤ ⊎ A

pred : ℕ → Maybe ℕ
pred zero = Nothing
pred (suc n) = Just n

-- HF:
zerosuc : Maybe ℕ → ℕ
zerosuc = {!!} -- inverze a pred-nek

{-
data ℤ : Type where
  zero : ℤ 
  suc  : Z → Z
  pred : Z → Z
  presuc : pred (suc n) ≡ n
  sucpred : suc (pred n) ≡ n
-}
