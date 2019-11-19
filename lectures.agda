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

    infixl 4 _+_
    infixl 5 _*_
    infixr 2 _≡⟨_⟩_
    infix  3 _∎

    _+_ : ℕ → ℕ → ℕ
    zero  + y = y
    suc x + y = suc (x + y)

    eq : ℕ → ℕ → Bool
    eq zero    zero    = true
    eq (suc x) zero    = false
    eq zero    (suc y) = false
    eq (suc x) (suc y) = eq x y

    toSet : Bool → Set
    toSet true  = ⊤
    toSet false = ⊥

    Eqn : ℕ → ℕ → Set
    Eqn x y = toSet (eq x y)

    refln : (x : ℕ) → Eqn x x
    refln zero = tt
    refln (suc x) = refln x

    transport : (P : ℕ → Set)(x y : ℕ) → Eqn x y → P x → P y
    transport P zero    zero    e u = u
    transport P (suc x) zero    e u = exfalso e
    transport P zero    (suc y) e u = exfalso e
    transport P (suc x) (suc y) e u = transport (λ x → P (suc x)) x y e u

    sym : (x y : ℕ) → Eqn x y → Eqn y x
    sym x y e = transport (λ z → Eqn z x) x y e (refln x)

    trans : (x y z : ℕ) → Eqn x y → Eqn y z → Eqn x z
    trans x y z e e' = transport (λ q → Eqn x q) y z e' e

    cong : (f : ℕ → ℕ)(x y : ℕ) → Eqn x y → Eqn (f x) (f y)
    cong f x y e = transport (λ y → Eqn (f x) (f y)) x y e (refln (f x))
    
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

    _*_ : ℕ → ℕ → ℕ
    zero * y = zero
    suc x * y = y + (x * y)

    ex1 : (x y : ℕ) → Eqn ((x + (y + zero)) + x) (2 * x + y)
    ex1 x y = trans ((x + (y + zero)) + x) (x + (x + 0) + y) (2 * x + y)
      (trans (x + (y + zero) + x) (x + x + y) (x + (x + 0) + y)
             (trans (x + (y + zero) + x) (x + y + x) (x + x + y)
                    (cong (λ z → x + z + x) _ _ (idr y))
                    (trans (x + y + x) (x + (y + x)) (x + x + y)
                           (ass x y x)
                           (trans (x + (y + x)) (x + (x + y)) (x + x + y)
                                  (cong (λ z → x + z) _ _ (comm y x))
                                  (sym (x + x + y) (x + (x + y)) (ass x x y)))))
             (cong (λ z → x + z + y) _ _ (sym (x + zero) x (idr x))))
      (refln (2 * x + y))

    ex1' : (x y : ℕ) → Eqn ((x + (y + zero)) + x) (2 * x + y)
    ex1' x y = trans ((x + (y + zero)) + x) _ _
      (trans (x + (y + zero) + x) _ _
             (trans (x + (y + zero) + x) _ _
                    (cong (λ z → x + z + x) _ _ (idr y))
                    (trans (x + y + x) _ _
                           (ass x y x)
                           (trans (x + (y + x)) _ _
                                  (cong (λ z → x + z) _ _ (comm y x))
                                  (sym (x + x + y) (x + (x + y)) (ass x x y)))))
             (cong (λ z → x + z + y) _ _ (sym (x + zero) x (idr x))))
      (refln (2 * x + y))

    ex1'' : (x y : ℕ) → Eqn ((x + (y + zero)) + x) (2 * x + y)
    ex1'' x y =
      (trans (x + (y + zero) + x) (x + y + x) (2 * x + y)
                                                                   (cong (λ z → x + z + x) _ _ (idr y))
      (trans (x + y + x) (x + (y + x)) (x + (x + zero) + y)
                                                                   (ass x y x)
      (trans (x + (y + x)) (x + (x + y)) (x + (x + zero) + y)
                                                                   (cong (λ z → x + z) _ _ (comm y x))
      (trans (x + (x + y)) (x + x + y) (x + (x + zero) + y)
                                                                   (sym (x + x + y) (x + (x + y)) (ass x x y))
      (trans (x + x + y) (x + (x + 0) + y) (x + (x + 0) + y)
                                                                   (cong (λ z → x + z + y) _ _ (sym (x + zero) x (idr x)))
      (refln (2 * x + y)))))))

    ex1''' : (x y : ℕ) → Eqn ((x + (y + zero)) + x) (2 * x + y)
    ex1''' x y =
      (trans (x + (y + zero) + x) _ _
                                                                   (cong (λ z → x + z + x) _ _ (idr y))
      (trans (x + y + x) _ _
                                                                   (ass x y x)
      (trans (x + (y + x)) _ _
                                                                   (cong (λ z → x + z) _ _ (comm y x))
      (trans (x + (x + y)) _ _
                                                                   (sym (x + x + y) _ (ass x x y))
      (trans (x + x + y) _ _
                                                                   (cong (λ z → x + z + y) _ _ (sym _ x (idr x)))
      (refln (2 * x + y)))))))

    _≡⟨_⟩_ : (x : ℕ){y z : ℕ} → Eqn x y → Eqn y z → Eqn x z
    x ≡⟨ p ⟩ q = trans x _ _ p q

    _∎ : (x : ℕ) → Eqn x x
    x ∎ = refln x

{-
    ex1 x y =
      (x + (y + zero)) + x
                               ≡⟨ {!!} ⟩
      x + (x + 0) + y
                               ≡⟨ refln _ ⟩
      2 * x + y ∎
-}
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
    insert x (suc l) (y , xs) = case (≤dec x y)
      (λ _ → x , y , xs)
      (λ _ → y , insert x l xs)

    _∧_ : Bool → Bool → Bool
    true  ∧ true = true
    _     ∧ _    = false

    eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Bool
    eq^ zero xs ys = true
    eq^ (suc l) (x , xs) (y , ys) = eq x y ∧ eq^ l xs ys

    Eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
    Eq^ l xs ys = toSet (eq^ l xs ys)

    test1 : Eq^ 5 (insert 3 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
    test1 = tt

    test2 : Eq^ 5 (insert 0 4 (1 , 2 , 4 , 5 , tt)) (0 , 1 , 2 , 4 , 5 , tt)
    test2 = tt

    test3 : Eq^ 5 (insert 1 4 (1 , 2 , 4 , 5 , tt)) (1 , 1 , 2 , 4 , 5 , tt)
    test3 = tt

    test4 : Eq^ 5 (insert 10 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 4 , 5 , 10 , tt)
    test4 = tt

    sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
    sort zero _ = tt
    sort (suc l) (x , xs) = insert x l (sort l xs)

    test5 : Eq^ 5 (sort 5 (3 , 2 , 1 , 5 , 4 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
    test5 = tt

    test6 : Eq^ 5 (sort 5 (2 , 2 , 1 , 4 , 4 , tt)) (1 , 2 , 2 , 4 , 4 , tt)
    test6 = tt

    Ordered : (l : ℕ) → ℕ ^ l → Set
    Ordered zero          xs           = ⊤
    Ordered (suc zero)    xs           = ⊤
    Ordered (suc (suc l)) (x , y , xs) = x ≤ y × Ordered (suc l) (y , xs)

    insert-Ordered : (l : ℕ)(xs : ℕ ^ l) → Ordered l xs → (y : ℕ) → Ordered (suc l) (insert y l xs)
    insert-Ordered zero          xs       o y = tt
    insert-Ordered (suc zero)    (x , xs) o y = {!!}
    insert-Ordered (suc (suc l)) (x , xs) o y = {!!}
