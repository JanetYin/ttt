{-

a
| \
c₀ c₁   
| /
b

a isGrandparentOf b = Σ Person λ c → a isParentOf c × c isParentOf b

TODO: everyone gets the point for Q2
-}

open import Lib hiding (_^_; id)

_^_ : Set → ℕ → Set
A ^ zero = ⊤
A ^ suc n = A × A ^ n

-- A ^ n ≅ (Fin n → A) ≅ Vec A n

pf : (n : ℕ){A : Set} →  A ^ n ≡ A ^ (n + 0)
pf n {A} = cong (A ^_) (sym (idr+ n))

-- p : ¬ (Bool ≡ ℕ)
-- refl : Bool ≡ Bool
-- ∅ : Bool ≡ ⊤ ⊎ ⊤            -- in homotopy type theory (Cubical Agda), we have a proof of this
-- ∅ : ¬ (Bool ≡ ⊤ ⊎ ⊤)        -- if we have a typecase operator, we have a proof of this

module m1 where
  -- typecase using a universe
  data U : Set where  -- these are codes for types
    cBool : U
    cℕ    : U
    _c×_  : U → U → U
    _c+_  : U → U → U
  -- this universe has types with decidable equality, but they are not necessarily finite

  El : U → Set  -- "El a" is the type of elements of "a"
  El cBool = Bool
  El cℕ = ℕ
  El (cA c× cB) = El cA × El cB
  El (cA c+ cB) = El cA ⊎ El cB

  id : (A : Set) → A → A    -- parametric polymorphism
  id A a = a

  id' : (cA : U) → El cA → El cA    -- ad-hoc polymorphism
  id' cBool a = not a
  id' cℕ a = suc a
  id' (cA c× cA₁) a = id' cA (id' cA (fst a)) , snd a
  id' (cA c+ cA₁) a = a

data isOdd : ℕ → Set
data isEven : ℕ → Set
data isOdd where
  suc  : {n : ℕ} → isEven n → isOdd (suc n)
data isEven where
  zero : isEven zero
  suc  : {n : ℕ} → isOdd n → isEven (suc n)

module m2 where
  data U : Set     -- these are codes for types
  El : U → Set
  data U where
    cBool : U
    cΣ    : (cA : U) → (El cA → U) → U      -- Σ : (A : Set) → (A → Set) → Set
    cΠ    : (cA : U) → (El cA → U) → U
  El cBool = Bool
  El (cΣ cA cB) = Σ (El cA) λ a → El (cB a)
  El (cΠ cA cB) = (a : El cA) → El (cB a)
  -- this universe has only finite types, hence all types in it have decidable equality

  decEq : (cA : U)(a a' : El cA) → a ≡ a' ⊎ ¬ (a ≡ a')
  decEq cA a a' = {!   !} -- this is provable, but quite complicated

idBool : Bool → Bool
idBool b = b

idBool' : Bool → Bool
idBool' true  = true
idBool' false = false

-- function extensionality for Bool: (f g : Bool) → ((b : Bool) → f b ≡ g b) → f ≡ g

negid : ¬ (not ≡ idBool)
negid h with cong (λ f → f true) h
... | ()

id=' : (λ x → idBool x) ≡ (λ x → idBool' x) -- I cannot prove this
id=' = {!!}
id= : idBool ≡ idBool'
id= = id='

dec4 : (f g : Bool → Bool) → f ≡ g ⊎ ¬ (f ≡ g)
dec4 = {!!}

-- look at computing types, e.g. _^_, and prove some equations about it

{-
Agda does not decide on:
- what is equality of types?
- what is equality of functions?
- do we have classical logic? (whether any type is decided)
- what is equality of coinductive types?
-}


