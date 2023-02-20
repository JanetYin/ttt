open import lib

-- ez az eloadas 2 perccel rovidebb

-- propositional vs definitional equality, first example: proofs about boolean or

-- osszeadas tulajdonsagai, egyenlosegi erveles

-- negativ allitasok szamokrol, pl. ¬ ((n : ℕ) → ¬ (n ≡ 1) → n ≡ 2)

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

transp : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
transp P refl p = p

kviz1 : ¬ ((R : ℕ → ℕ → Type) → (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) → Σ ℕ (λ x → R x x)))
kviz1 f = g (fst (f R w)) (snd (f R w))
  where
    R : ℕ → ℕ → Type
    R zero (suc zero) = ⊤
    R _ _ = ⊥
    g : (x : ℕ) → R x x → ⊥
    g zero r = r
    g (suc x) r = r
    w : Σ ℕ (λ x → Σ ℕ (λ y → R x y))
    w = 0 , 1 , tt

module es1 where
  _∧_ : Bool → Bool → Bool
  true ∧ b = b      -- definicio szerinti egyenloseg
  false ∧ b = false

  idl : (x : Bool) → true ∧ x ≡ x  -- egyenloseg tipus szerinti egyenloseg, propozionalis egyenloseg, tipus-szerinti egyenloseg
  idl x = refl

  idr : (x : Bool) → x ∧ true ≡ x
  idr false = refl
  idr true = refl

module es2 where
  _∧_ : Bool → Bool → Bool
  a ∧ true = a
  a ∧ false = false

  idr : (x : Bool) → x ∧ true ≡ x
  idr x = refl

module es3 where
  _∧_ : Bool → Bool → Bool
  false ∧ false = false
  false ∧ true  = false
  true  ∧ false = false
  true  ∧ true  = true

idl : (n : ℕ) → zero + n ≡ n
idl = λ n → refl

idr : (n : ℕ) → n + zero ≡ n
idr zero = refl
idr (suc n) = cong suc (idr n)

ass : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass zero n o = refl
ass (suc m) n o = cong suc (ass m n o)
-- ((suc m) + n) + o = (suc (m + n)) + o = suc ((m + n) + o)

-- P : ℕ → Type                 P m := (m + n) + o ≡ m + (n + o)
-- P zero                       P zero = n + o ≡ n + o
-- (m : ℕ) → P m → P (suc m)    suc ((m + n) + o) ≡ suc (m + (n + o))
----------------------------
-- (n : ℕ) → P n

ind : (P : ℕ → Type) → P zero → ((n : ℕ) → P n → P (suc n)) →
   (n : ℕ) → P n
ind P pz ps zero = pz
ind P pz ps (suc n) = ps n (ind P pz ps n)

comm : (m n : ℕ) → m + n ≡ n + m
comm = {!!}

-- kovetkezo eloadas 5 perccel rovidebb
