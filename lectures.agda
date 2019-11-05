module lectures where

open import lib

module first where

  not : Bool → Bool
  not = λ x → if x then false else true

  plus : ℕ → ℕ → ℕ
  plus = λ x y → primrec y (λ _ n → suc n) x

  eq : ℕ → ℕ → Bool
  eq = λ x → primrec is0 (λ _ → f) x
    where
      is0 : ℕ → Bool
      is0 = λ y → primrec true (λ _ _ → false) y
      f : (ℕ → Bool) → (ℕ → Bool)
      f = λ isn → λ y → primrec false (λ y' _ → isn y') y

  eqb : Bool → Bool → Bool
  eqb = λ x y → if x then y else not y

  _^_ : Set → ℕ → Set
  _^_ = λ A n → primrec ⊤ (λ _ As → A × As) n

  Eqb : Bool → Bool → Set
  Eqb = λ x y → if x then (if y then ⊤ else ⊥) else (if y then ⊥ else ⊤)

  true=true : Eqb true true
  true=true = tt

  ¬true=false : ¬ Eqb true false
  ¬true=false = λ e → e

  notUnitTest : Eqb (not (not true)) true
  notUnitTest = tt

  notInvolutive : (x : Bool) → Eqb (not (not x)) x
  notInvolutive = λ x → indBool (λ y → Eqb (not (not y)) y) tt tt x

  Eqn : ℕ → ℕ → Set
  Eqn = λ x y → Eqb (eq x y) true

  testEqnZero : Eq Set (Eqn zero zero) ⊤
  testEqnZero = refl

  testEqnSuc : {x y : ℕ} → Eq Set (Eqn (suc x) (suc y)) (Eqn x y)
  testEqnSuc = refl

  plusLeftId : (x : ℕ) → Eqn (plus zero x) x
  plusLeftId = λ x → indℕ (λ x → Eqn x x) tt (λ _ e → e) x

  plusRightId : (x : ℕ) → Eqn (plus x zero) x
  plusRightId = λ x → indℕ (λ x → Eqn (plus x zero) x) tt (λ _ e → e) x

  zero≠suc : (x : ℕ) → ¬ Eqn zero (suc x)
  zero≠suc = λ x e → e

  suc-inj : (x y : ℕ) → Eqn (suc x) (suc y) → Eqn x y
  suc-inj = λ x y e → e

module patternMatching where

    _+_ : ℕ → ℕ → ℕ
    zero  + y = y
    suc x + y = suc (x + y)
    
    Eqn : ℕ → ℕ → Set
    Eqn zero    zero    = ⊤
    Eqn (suc x) zero    = ⊥
    Eqn zero    (suc y) = ⊥
    Eqn (suc x) (suc y) = Eqn x y

    refln : (x : ℕ) → Eqn x x
    refln zero = tt
    refln (suc x) = refln x

    transp : (P : ℕ → Set)(x y : ℕ) → Eqn x y → P x → P y
    transp P zero    zero    e u = u
    transp P (suc x) zero    e u = exfalso e
    transp P zero    (suc y) e u = exfalso e
    transp P (suc x) (suc y) e u = transp (λ x → P (suc x)) x y e u

    sym : (x y : ℕ) → Eqn x y → Eqn y x
    sym x y e = transp (λ z → Eqn z x) x y e (refln x)

    trans : (x y z : ℕ) → Eqn x y → Eqn y z → Eqn x z
    trans x y z e e' = transp (λ q → Eqn x q) y z e' e

    -- 

    zero≠suc : (x : ℕ) → ¬ Eqn zero (suc x)
    zero≠suc x e = e

    suc-inj : (x y : ℕ) → Eqn (suc x) (suc y) → Eqn x y
    suc-inj x y e = e

    -- 

    idl : (x : ℕ) → Eqn (zero + x) x
    idl x = refln x

    idr : (x : ℕ) → Eqn (x + zero) x
    idr zero    = tt
    idr (suc x) = idr x

    ass : (x y z : ℕ) → Eqn ((x + y) + z) (x + (y + z))
    ass zero    y z = refln (y + z)
    ass (suc x) y z = ass x y z

    comm-lemm : (x y : ℕ) → Eqn (suc x + y) (x + suc y)
    comm-lemm zero    y = refln y
    comm-lemm (suc x) y = comm-lemm x y

    comm : (x y : ℕ) → Eqn (x + y) (y + x)
    comm zero y    = sym (y + zero) y (idr y)
    comm (suc x) y = trans (suc (x + y)) (suc (y + x)) (y + suc x) (comm x y) (comm-lemm y x)

    _≤_ : ℕ → ℕ → Set
    zero  ≤ y     = ⊤
    suc x ≤ zero  = ⊥
    suc x ≤ suc y = x ≤ y

    ex : 3 ≤ 100
    ex = tt
    
    refl≤ : (x : ℕ) → x ≤ x
    refl≤ zero = tt
    refl≤ (suc x) = refl≤ x

    trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
    trans≤ zero    y       z       e e' = tt
    trans≤ (suc x) (suc y) (suc z) e e' = trans≤ x y z e e'

    ≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
    ≤dec zero y = inj₁ tt
    ≤dec (suc x) zero = inj₂ tt
    ≤dec (suc x) (suc y) = ≤dec x y

    _^_ : Set → ℕ → Set
    A ^ zero  = ⊤
    A ^ suc x = A × A ^ x

    insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
    insert x zero    xs       = x , tt
    insert x (suc l) (y , xs) with ≤dec x y
    insert x (suc l) (y , xs) | inj₁ e = x , y , xs
    insert x (suc l) (y , xs) | inj₂ e = y , insert x l xs

    Eqℕ^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
    Eqℕ^ zero xs ys = ⊤
    Eqℕ^ (suc l) (x , xs) (y , ys) = Eqn x y × Eqℕ^ l xs ys

    ⊤s : (x : ℕ) → ⊤ ^ x
    ⊤s zero    = tt
    ⊤s (suc x) = tt , ⊤s x

    test : Eqℕ^ 5 (insert 3 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
    test = ⊤s 5

    
