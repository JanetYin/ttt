open import Lib hiding (_$_;_$'_;proj;_<_)
open import SK.php

module SK.Church_encoding where

-- infixl 5 _·_

record Model : Set₁ where
  infixl 5 _·_ 
  field
    Tm  : Set
    _·_ : Tm → Tm → Tm
    K S : Tm
    Kβ  : ∀{u f} → K · u · f ≡ u
    Sβ  : ∀{f g u} → S · f · g · u ≡ f · u · (g · u)




module Syn where 
  infixl 5 _·_  
  postulate
    Tm  : Set
    _·_ : Tm → Tm → Tm
    K S : Tm
    Kβ  : ∀{u f} → K · u · f ≡ u
    Sβ  : ∀{f g u} → S · f · g · u ≡ f · u · (g · u)
    -- K

Syn' : Model
Syn' = record { Tm = Syn.Tm ; _·_ = Syn._·_ ; K = Syn.K ; S = Syn.S ; Kβ = Syn.Kβ ; Sβ = Syn.Sβ }
module Syn' = Model Syn'

-- module InitialModel (m : Model) where
--   open Model m
  
--   ⟦_⟧ : Syn.Tm → Tm
--   ⟦ Syn.K ⟧ = K --⟦ Syn.K ⟧ ≡ K
--   ⟦ Syn.S ⟧ = S --⟦ Syn.S ⟧ ≡ S
--   ⟦ a Syn.· b ⟧ = {!   !}
-- data _—→_ : Tm → Tm → Set where
-- module reduction (m : Model) where 
--         open Model m 
--         infix 4 _—→_

        
        
          
module programmingWithCombinators (m : Model) where
  open Model m
  infixl 5 _·s_
  
  I : Tm
  I = S · K · K
  Iβ : ∀{u} → I · u ≡ u
  Iβ {u} =
    (I · u)
              ≡⟨ refl ⟩ 
    (((S · K) · K) · u)
              ≡⟨ Sβ ⟩ 
    ((K · u) · (K · u))
              ≡⟨ Kβ ⟩ 
    refl
    
  
  B : Tm
  B = S · (K · S) · K
  Bβ : ∀{f g u} → B · f · g · u ≡ f · (g · u)
  Bβ {f}{g}{u} = 
    (B · f · g · u)
              ≡⟨ refl ⟩ 
    (S · (K · S) · K · f · g · u)
              ≡⟨ cong (λ z → z · g · u) Sβ ⟩ 
    (K · S · f · (K · f) · g · u)
              ≡⟨ cong (λ z → z · (K · f) · g · u) Kβ ⟩ 
    (S · (K · f) · g · u)
               ≡⟨ Sβ ⟩ 
    (K · f · u · (g · u))          
               ≡⟨ cong (λ z → z · (g · u)) Kβ ⟩ 
    refl


  C : Tm
  C = S · (B · B · S) · (K · K) 
  Cβ : ∀{f g u} → C · f · u · g ≡ f · g · u
  Cβ {f}{g}{u} = 
    (C · f · u · g) 
              ≡⟨ refl ⟩ 
    (S · (B · B · S) · (K · K) · f ·  u · g)
              ≡⟨ cong (λ z → z · u · g) Sβ ⟩ 
    (B · B · S · f · (K · K · f) ·  u · g)    
              ≡⟨ cong (λ z → z  · (K · K · f) ·  u · g) Bβ ⟩ 
    (B · (S · f) · (K · K · f) ·  u · g)
              ≡⟨  cong (λ z → z  · g) Bβ  ⟩ 
    (S · f · ((K · K · f) ·  u)  · g)
              ≡⟨ cong (λ z → (S · f) · (z · u)  · g) Kβ  ⟩ 
    (S · f · (K ·  u) · g)
              ≡⟨ Sβ ⟩ 
    (f · g ·  (K ·  u · g))
              ≡⟨ cong (λ z → f · g · z) Kβ ⟩ 
    refl


  M : Tm
  M = S · I · I
  Mβ : ∀{f} → M · f ≡ f · f
  Mβ {f} =
     (M · f)
              ≡⟨ refl ⟩ 
     (S · I · I · f)
              ≡⟨ Sβ ⟩ 
     ((I · f) · (I · f))
              ≡⟨ cong (λ z → z · z) Iβ ⟩ 
     refl


  L : Tm
  L = C · B · M
  Lβ : ∀{f g} → L · f · g ≡ f · ( g · g )
  Lβ {f}{g}=
      (L · f · g)
              ≡⟨ refl ⟩ 
      (C · B · M · f · g)
              ≡⟨ cong (λ z → z · g) Cβ ⟩ 
      (B ·  f · M · g)
              ≡⟨ Bβ ⟩ 
      (f · (M · g))
              ≡⟨ cong (λ z → f · z) Mβ ⟩ 
      refl

  --· ( S · L · L · f)
  -- x is a fixpoint of f if "f · x = x"
    -- in lambda calculus: λf.(λx.f(x x))(λx.f(x x))
  -- EXE: bit harder
  Y : Tm
  Y = S · L · L
  Yβ : ∀{f} → Y · f ≡ f · (Y · f)
  Yβ {f} =
      (Y · f)
              ≡⟨ refl ⟩ 
      (S · L · L · f)
              ≡⟨ Sβ ⟩ 
      (L · f · (L · f))
              ≡⟨ Lβ ⟩ 
      (f · ((L · f) · (L · f)))
              ≡⟨ cong (λ z → f · z) (sym Sβ) ⟩ 
      refl
              

  zero' : Tm
  zero' = K
  zeroβ : ∀{z s} → zero' · z · s ≡ z
  zeroβ = Kβ

  one : Tm
  one = C · I  
  oneβ : ∀{z s} → one · z · s ≡ s · z
  oneβ {z}{s} = 
      (one · z · s)
              ≡⟨ refl ⟩ 
      (C · I · z · s)
              ≡⟨ Cβ ⟩ 
      (I · s · z)
              ≡⟨ cong (λ x → x · z) Iβ ⟩ 
      refl
  
   -- 

  succ : Tm
  succ =  B · (S · I)
  sucβ : ∀{n z s} → succ · n · z · s ≡ s · (n · z · s) -- \n f x -> f(n f x)
  sucβ {n}{z}{s}= 
      (succ · n · z · s)
              ≡⟨ refl ⟩ 
      (B · (S · I) · n · z · s)
              ≡⟨ cong  (λ x → x · s ) Bβ ⟩ 
      (S · I · (n · z) · s)
              ≡⟨ Sβ ⟩ 
      (I · s · (n · z · s))
              ≡⟨ cong (λ x → x  · (n · z · s) ) Iβ ⟩ 
      refl
  

  R : Tm
  R = B · B · one
  Rβ : ∀{n z s} → R · n · z · s ≡ z · s · n
  Rβ {n}{z}{s}= 
    cong (λ x → x · z · s) Bβ ◾
    cong (λ x → x) Bβ ◾
    cong (λ x → x) oneβ 

  iszero : Tm
  iszero = R · (K  · (S · K)) · (C · I · K)
  
  -- iszeroβ :\n -> n true (\x -> false) = R(K false)(T true)

  iszeroβ' :  iszero · zero' ≡ K --K₁ (K₁ (S₂ K₀ K₀))
  iszeroβ' = 
      (iszero · zero')
              ≡⟨ refl ⟩ 
      (R · (K  · (S · K)) · (C · I · K) · K)
              ≡⟨  Rβ ⟩ 
      (C · I · K · K · (K  · (S · K)))
              ≡⟨ cong (λ z → z ·  (K · (S · K)) ) Cβ ⟩ 
      (I · K · K · (K  · (S · K)))
              ≡⟨ cong (λ z → z · K · (K · (S · K)) ) Iβ ⟩ 
      (K · K · (K · (S · K)))
              ≡⟨ zeroβ ⟩ 
      refl

  iszeroβ'' : ∀ {n} → iszero · (succ · n) ≡ S · K
  iszeroβ'' {n} = 
      (iszero · (succ · n))
              ≡⟨ refl ⟩ 
      (R · (K  · (S · K)) · (C · I · K) · (succ · n))
              ≡⟨  Rβ ⟩ 
      (C · I · K · (succ · n) · (K  · (S · K)))
              ≡⟨ cong (λ z → z ·  (K · (S · K)) ) Cβ ⟩ 
      (I · (succ · n) · K · (K  · (S · K)))
              ≡⟨ cong (λ z → z · K · (K · (S · K)) ) Iβ ⟩ 
      (succ · n · K · (K  · (S · K)))
              ≡⟨ sucβ ⟩ 
      (K  · (S · K) ·  (n · K · (K  · (S · K))))
              ≡⟨ Kβ ⟩ 
      refl
      
    -- cong (λ z → z ) Rβ  ◾
    -- cong (λ z → z ·  (K · (S · K)) ) Cβ  ◾
    -- cong (λ i → i · K · (K · (S · K)) ) Iβ  ◾
    -- cong (λ z → z ) sucβ  ◾
    -- Kβ
  
    -- Sβ ◾
    -- Lβ ◾ 
    -- cong (λ z → f · z) (sym Sβ)

    -- cong (λ z → z · (K · (S · f)) · ((K · K) · f) · u · g) Kβ ◾
    -- cong (λ z → z · g) Sβ ◾
    -- cong (λ z → z · (((K · K) · f) · u) · g ) Kβ ◾
    -- cong (λ z → (S · f) · (z · u) · g )  Kβ ◾
    -- Sβ ◾
    -- cong (λ z → (f · g) · z) Kβ
  
  kTm : Tm 
  kTm = S · (K · K) · (S · K · K)
  kTmβ : ∀ {x y} → kTm · x · y ≡ x 
  kTmβ {x} {y} = 
    cong (λ z → z · y) Sβ ◾
    cong (λ z → z · (S · K · K · x) · y) Kβ ◾
    cong (λ z → z ) Kβ ◾
    cong (λ z → z ) Sβ ◾
    Kβ

  _·s_ : Tm → {n : ℕ} → Vec Tm n → Tm
  _·s_ t {zero}  [] = t
  _·s_ t {suc n} (u ∷ us)  = t · u ·s us

  lookup : {A : Set }{n : ℕ} → Vec A n → Fin n → A
  lookup (x ∷ xs) fzero    = x
  lookup (x ∷ xs) (fsuc i) = lookup xs i
  
  proj : (n : ℕ) → Fin n → Tm
  proj (suc zero)    fzero    = I
  proj (suc (suc n)) fzero    = B · K · proj (suc n) fzero
  proj (suc (suc n)) (fsuc x) = K · proj (suc n) x

  projβ : (n : ℕ)(x : Fin n)(us : Vec Tm n) → proj n x ·s us ≡ lookup us x
  projβ (suc zero)    fzero    (u ∷ [])      = Iβ
  projβ (suc (suc n)) fzero    (u ∷ u' ∷ us) = (B · K · (proj (suc n) fzero) · u · u' ·s us)
                                                          ≡⟨ cong (λ z → z · u' ·s us) Bβ ⟩ 
                                                (K · (proj (suc n) fzero · u) · u' ·s us)
                                                          ≡⟨ cong (_·s us) Kβ ⟩ 
                                                (proj (suc n) fzero · u ·s us)
                                                          ≡⟨ projβ (suc n) fzero (u ∷ us) ⟩ 
                                                refl
  projβ (suc (suc n)) (fsuc x) (u ∷ u' ∷ us) =  (K · proj (suc n) x · u · u' ·s us)
                                                        ≡⟨ cong (λ x → x · u' ·s us) Kβ ⟩ 
                                                (proj (suc n) x · u' ·s us)
                                                        ≡⟨ projβ (suc n) x (u' ∷ us) ⟩ 
                                                refl
                                              
         
  fst₄ = proj 4 fzero
  fst₄β : ∀ {a b c d} → fst₄ · a · b · c · d ≡ a
  fst₄β {a}{b}{c}{d} =  
        cong  (λ z → (z · b) · c · d) Bβ ◾
        cong  (λ z → z · c · d ) Kβ ◾
        cong  (λ z → z · c · d) Bβ ◾
        cong  (λ z → z · d ) Kβ ◾
        cong  (λ z → z · d ) Bβ ◾
        Kβ ◾
        Iβ

  thd₄ : Tm 
  thd₄ = proj 4 (fsuc (fsuc fzero))
  thd₄β : ∀ {a b c d} → thd₄ · a · b · c · d ≡ c
  thd₄β {a}{b}{c}{d} =
        cong   (λ z → (z · b) · c · d) Kβ ◾
        cong   (λ z → z · c · d) Kβ ◾
        cong   (λ z → z · d) Bβ ◾
        cong   (λ z → z) Kβ ◾
        Iβ

  -- Zero : Tm 
  -- Zero = K · I
  -- Zeroβ :  ∀{f x} → Zero · f · x ≡ x
  -- Zeroβ {f}{x} = 
  --   cong (λ z → z · x) Kβ ◾
  --   Iβ

  -- One : Tm 
  -- One = I
  -- Oneβ : ∀{f x} → One · f · x ≡ f · x
  -- Oneβ {f}{x} =
  --   cong (λ z → z · x) Sβ ◾
  --   cong (λ z → z · x  ) Kβ

  -- Suc : Tm 
  -- Suc = S · B 
  -- Sucβ : ∀{n f x} → Suc · n · f · x ≡ f · (n · f · x)
  -- Sucβ {n}{f}{x} = 
  --   cong (λ z → z · x) Sβ ◾
  --   Bβ
module notBoolModel2
  (_·_ :  Fin 2 → Fin 2 → Fin 2)
  (let infixl 5 _·_; _·_ = _·_)
  (K S :  Fin 2)
  (Kβ : {u f : Fin 2} → (K · u) · f ≡ u)
  (Sβ :  {f g u : Fin 2} → ((S · f) · g) · u ≡ (f · u) · (g · u))

  where

  Tm = Fin 2
  infixl 5 _·s_
  B : Tm
  B = S · (K · S) · K
  Bβ : ∀{f g u} → B · f · g · u ≡ f · (g · u)
  Bβ {f}{g}{u} = 
    cong (λ z → (z · g) · u) Sβ ◾
    cong (λ z → ((z · (K · f)) · g) · u) Kβ ◾
    Sβ ◾
    cong (λ z → z · (g · u)) Kβ

  I : Tm
  I = S · K · K
  Iβ : ∀{u} → I · u ≡ u
  Iβ {u} =
    Sβ ◾
    Kβ 

  _·s_ : Tm → {n : ℕ} → Vec Tm n → Tm
  _·s_ t {zero}  [] = t
  _·s_ t {suc n} (u ∷ us)  = t · u ·s us

  lookup : {A : Set }{n : ℕ} → Vec A n → Fin n → A
  lookup (x ∷ xs) fzero    = x
  lookup (x ∷ xs) (fsuc i) = lookup xs i
  
  proj : (n : ℕ) → Fin n → Tm
  proj (suc zero)    fzero    = I
  proj (suc (suc n)) fzero    = B · K · proj (suc n) fzero
  proj (suc (suc n)) (fsuc x) = K · proj (suc n) x

  projβ : (n : ℕ)(x : Fin n)(us : Vec Tm n) → proj n x ·s us ≡ lookup us x
  projβ (suc zero) fzero (x ∷ []) = Iβ
  projβ (suc (suc n)) fzero (u ∷ u' ∷ us) = trans ((cong (λ z → z · u' ·s us) Bβ)) (trans (cong (λ z → z ·s us) Kβ) (projβ (suc n) fzero (u ∷ us))) -- trans (cong (λ z → z) Bβ) {!  (cong (λ z → z) Kβ) !} --trans (cong (λ z → z) Bβ) {!   !}
  projβ (suc (suc n)) (fsuc x) (u ∷ u' ∷ us) = trans ((cong (λ x → x · u' ·s us) Kβ)) (projβ (suc n) x (u' ∷ us))

  f : Fin 3 → Fin 2
  f x = proj 3 x 

  fromPigeon' : (f : Fin 3 → Fin 2) → ∃₂ λ i j → i ≢ j × f i ≡ f j 
  fromPigeon' f = pigeonhole (s≤s (s≤s (s≤s z≤n))) f
  
  apply : ∃₂ λ i j → i ≢ j × f i ≡ f j 
  apply = fromPigeon' f 

  case1 : proj 3 fzero ≡ proj 3 (fsuc fzero) → ((proj 3 fzero) ·  fzero · ( fsuc fzero ) · (fsuc fzero )) ≡ (proj 3 (fsuc fzero)  · fzero · ( fsuc fzero ) · ( fsuc fzero ))
  case1 = λ x → cong (λ f → f ·  (fzero) · ( fsuc fzero ) · ( fsuc fzero )) x
  case1' : proj 3 fzero ≡ proj 3 (fsuc fzero) → fzero ≡ fsuc fzero
  case1' x = trans (sym (projβ 3 fzero (fzero ∷ (fsuc fzero  ∷ (fsuc fzero  ∷ []))))) (trans (case1 x) (projβ 3 (fsuc fzero) (fzero ∷ (fsuc fzero  ∷ (fsuc fzero  ∷ []))))) 

  case2 : proj 3 fzero ≡  proj 3 (fsuc (fsuc fzero)) → ((proj 3 fzero · fzero) · (fsuc fzero)) · (fsuc fzero) ≡ ((proj 3 (fsuc (fsuc fzero)) · fzero) · (fsuc fzero)) · (fsuc fzero)
  case2 = λ x → cong (λ f → ((f ·  fzero) · (fsuc fzero)) · (fsuc fzero)) x
  case2' : proj 3 fzero ≡ proj 3 (fsuc (fsuc fzero)) →  fzero ≡ fsuc fzero
  case2'  x = trans (sym (projβ 3 fzero ( fzero ∷ ((fsuc fzero) ∷ ((fsuc fzero) ∷ []))))) (trans (case2 x) ((projβ 3 (fsuc (fsuc fzero)) ( fzero ∷ ((fsuc fzero) ∷ ((fsuc fzero) ∷ [])))))) 

  case3 : proj 3 (fsuc fzero) ≡ proj 3 (fsuc (fsuc fzero)) → (proj 3 (fsuc fzero)) · (fsuc fzero) · fzero · (fsuc fzero) ≡ (proj 3 (fsuc (fsuc fzero))) · (fsuc fzero) · fzero · (fsuc fzero) 
  case3 =   λ x → cong (λ f → ((f · (fsuc fzero)) · fzero) · (fsuc fzero)) x
  case3' :  proj 3 (fsuc fzero) ≡ proj 3 (fsuc (fsuc fzero)) →  fzero ≡ fsuc fzero
  case3' x =  trans (sym (projβ 3 (fsuc fzero) ((fsuc fzero) ∷ (fzero ∷ ((fsuc fzero) ∷ []))))) (trans (case3 x) (projβ 3 (fsuc (fsuc fzero)) ((fsuc fzero) ∷ (fzero ∷ ((fsuc fzero) ∷ []))))) 


  contra : fzero ≡ fsuc fzero
  contra with apply
  ... | fzero , fzero , i≠j , fi=fj = exfalso (i≠j refl)
  ... | fzero , fsuc fzero , i≠j , fi=fj = case1' fi=fj
  ... | fzero , fsuc (fsuc fzero) , i≠j , fi=fj = case2' fi=fj
  ... | fsuc fzero , fzero , i≠j , fi=fj = case1' (sym fi=fj)
  ... | fsuc fzero , fsuc fzero , i≠j , fi=fj = exfalso (i≠j refl)
  ... | fsuc fzero , fsuc (fsuc fzero) , i≠j , fi=fj = case3' fi=fj 
  ... | fsuc (fsuc fzero) , fzero , i≠j , fi=fj = case2' (sym fi=fj)
  ... | fsuc (fsuc fzero) , fsuc fzero , i≠j , fi=fj = case3' (sym fi=fj)
  ... | fsuc (fsuc fzero) , fsuc (fsuc fzero) , i≠j , fi=fj = exfalso (i≠j refl)

  bot : ⊥
  bot with contra
  bot | ()


module notFiniteModel
  (m : ℕ)
  (n : ℕ)
  -- (n = suc (suc m))
  (_·_ :  Fin n → Fin n → Fin  n)
  (let infixl 5 _·_; _·_ = _·_)
  (K S :  Fin n)
  (Kβ : {u f : Fin n} → (K · u) · f ≡ u)
  (Sβ :  {f g u : Fin n} → ((S · f) · g) · u ≡ (f · u) · (g · u))

  where
    -- infixl 5 _·_
    -- n = suc (suc m)
    Tm = Fin n 
    infixl 5 _·s_
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

    Zero : Tm 
    Zero = K · I
    Zeroβ :  ∀{f x} → Zero · f · x ≡ x
    Zeroβ {f}{x} = 
        cong (λ z → z · x) Kβ ◾
        Iβ

    One : Tm 
    One = I
    Oneβ : ∀{f x} → One · f · x ≡ f · x
    Oneβ {f}{x} =
        cong (λ z → z · x) Sβ ◾
        cong (λ z → z · x  ) Kβ

    Suc : Tm 
    Suc = S · B 
    Sucβ : ∀{n f x} → Suc · n · f · x ≡ f · (n · f · x)
    Sucβ {n}{f}{x} = 
        cong (λ z → z · x) Sβ ◾
        Bβ

    _·s_ : Tm → {n : ℕ} → Vec Tm n → Tm
    _·s_ t {zero}  [] = t
    _·s_ t {suc n} (u ∷ us)  = t · u ·s us

    lookup : {A : Set }{n : ℕ} → Vec A n → Fin n → A
    lookup (x ∷ xs) fzero    = x
    lookup (x ∷ xs) (fsuc i) = lookup xs i
    
    -- {!   !}
    --           ≡⟨ {!   !} ⟩ 
    -- {!   !}
    --           ≡⟨ {!   !} ⟩ 
    -- {!   !}
    --           ≡⟨ {!  !} ⟩ 
    -- {!   !}
    proj : (n : ℕ) → (Fin n) → Tm
    proj (suc zero)    fzero    = I
    proj (suc (suc n)) fzero    = B · K · proj (suc n) fzero
    proj (suc (suc n)) (fsuc x) = K · proj (suc n) x

    projβ : (n : ℕ)(x : Fin n)(us : Vec Tm n) → proj n x ·s us ≡ lookup us x
    projβ (suc zero)    fzero    (u ∷ [])      = Iβ
    projβ (suc (suc n)) fzero    (u ∷ u' ∷ us) = trans (cong (λ x → x · u' ·s us) Bβ) (trans (cong (_·s us) Kβ) (projβ (suc n) fzero (u ∷ us))) 
    projβ (suc (suc n)) (fsuc x) (u ∷ u' ∷ us) = trans (cong (λ x → x · u' ·s us) Kβ) (projβ (suc n) x (u' ∷ us)) 

    f : Fin (suc n) → Fin n
    f x = proj (suc n) x 
    
    m≤sucm : {m : ℕ} → m < (suc m)
    m≤sucm {zero} = s≤s z≤n
    m≤sucm {suc m} = s≤s m≤sucm
  
    fromPigeon' : ∃₂ λ i j → i ≢ j × f i ≡ f j 
    fromPigeon'  = pigeonhole m≤sucm f 

module notFiniteModel2
  (m : ℕ)
  (_·_ :  Fin (suc (suc m)) → Fin (suc (suc m)) → Fin (suc (suc m)))
  (let infixl 5 _·_; _·_ = _·_)
  (K S :  Fin (suc (suc m)))
  (Kβ : {u f : Fin (suc (suc m))} → (K · u) · f ≡ u)
  (Sβ :  {f g u : Fin (suc (suc m))} → ((S · f) · g) · u ≡ (f · u) · (g · u))

  where

    n = suc (suc m)
    Tm = Fin n

    infixl 5 _·s_
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

    Zero : Tm 
    Zero = K · I
    Zeroβ :  ∀{f x} → Zero · f · x ≡ x
    Zeroβ {f}{x} = 
        cong (λ z → z · x) Kβ ◾
        Iβ

    One : Tm 
    One = I
    Oneβ : ∀{f x} → One · f · x ≡ f · x
    Oneβ {f}{x} =
        cong (λ z → z · x) Sβ ◾
        cong (λ z → z · x  ) Kβ

    Suc : Tm 
    Suc = S · B 
    Sucβ : ∀{n f x} → Suc · n · f · x ≡ f · (n · f · x)
    Sucβ {n}{f}{x} = 
        cong (λ z → z · x) Sβ ◾
        Bβ

    _·s_ : Tm → {n : ℕ} → Vec Tm n → Tm
    _·s_ t {zero}  [] = t
    _·s_ t {suc n} (u ∷ us)  = t · u ·s us

    lookup : ∀{ℓ}{A : Set ℓ}{n : ℕ} → Vec A n → Fin n → A
    lookup (x ∷ xs) fzero    = x
    lookup (x ∷ xs) (fsuc i) = lookup xs i
    
    proj : ∀(k : ℕ) → Fin (suc k) → Tm
    proj zero fzero = I
    proj (suc n₁) fzero = B · K · proj  n₁ fzero
    proj (suc n₁) (fsuc x) = K · proj n₁ x

    m≤sucm : {m : ℕ} → m < (suc m)
    m≤sucm {zero} = s≤s z≤n
    m≤sucm {suc m} = s≤s m≤sucm

    almost0 : {j : Fin (suc n)} → Fin (suc n) → Tm
    almost0 {j} x with x ≟ j
    ... | inr b = fzero
    ... | inl a = fsuc fzero

    flatten : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (Fin n → A) → Vec A n
    flatten {n = zero}  f = []
    flatten {n = suc n} f = f fzero ∷ flatten {n = n} (f ∘ fsuc)

    us : {j : Fin (suc n)} → Vec Tm (suc n)
    us {j} = flatten (almost0 {j})

  --    projβ : (n : ℕ)(x : Fin n)(us : Vec Tm n) → proj n x ·s us ≡ lookup us x
  -- projβ (suc zero)    fzero    (u ∷ [])      = Iβ
  -- projβ (suc (suc n)) fzero    (u ∷ u' ∷ us) = (B · K · (proj (suc n) fzero) · u · u' ·s us)
  --                                                         ≡⟨ cong (λ z → z · u' ·s us) Bβ ⟩ 
  --                                               (K · (proj (suc n) fzero · u) · u' ·s us)
  --                                                         ≡⟨ cong (_·s us) Kβ ⟩ 
  --                                               (proj (suc n) fzero · u ·s us)
  --                                                         ≡⟨ projβ (suc n) fzero (u ∷ us) ⟩ 
  --                                               refl
  -- projβ (suc (suc n)) (fsuc x) (u ∷ u' ∷ us) =  (K · proj (suc n) x · u · u' ·s us)
  --                                                       ≡⟨ cong (λ x → x · u' ·s us) Kβ ⟩ 
  --                                               (proj (suc n) x · u' ·s us)
  --                                                       ≡⟨ projβ (suc n) x (u' ∷ us) ⟩ 
  --                                               refl

    projβ : (n : ℕ)(x : Fin (suc n))(us : Vec Tm (suc n)) → proj n x ·s us ≡ lookup us x
    projβ zero fzero (u ∷ []) = Iβ
    projβ (suc n) fzero (u ∷ u' ∷ us) = (B · K · (proj n fzero) · u · u' ·s us)
                                                  ≡⟨ cong (λ x → (x · u') ·s us) Bβ ⟩ 
                                        (((K · (proj n fzero · u)) · u') ·s us)
                                                  ≡⟨ cong (_·s us) Kβ ⟩ 
                                        ((proj n fzero · u) ·s us)
                                                  ≡⟨ projβ n fzero (u ∷ us) ⟩ 
                                        refl

    projβ (suc n) (fsuc x) (u ∷ u' ∷ us) =  (K · (proj n x)  · u · u' ·s us)
                                                  ≡⟨ cong (λ x → x · u' ·s us) Kβ ⟩ 
                                            (proj n x · u' ·s us)
                                                  ≡⟨ projβ n x (u' ∷ us) ⟩ 
                                            refl
                                     
    flattenval : ∀{ℓ}{A : Set ℓ}{n : ℕ}(f : Fin n → A)(x : Fin n) → f x ≡ lookup (flatten f) x 
    flattenval {n = suc n} f fzero    = refl
    flattenval {n = suc n} f (fsuc x) = flattenval {n = n} (f ∘ fsuc) x

    almost0i : ∀{i j : Fin (suc n)} → i ≢ j → almost0 {j} i ≡ fzero
    almost0i {i}{j} i≠j with i ≟ j
    ... | inr b = refl
    ... | inl a with i≠j a
    ... | ()

    almost0j :  ∀{j : Fin (suc n)} → almost0 {j} j ≡ (fsuc fzero)
    almost0j {j} with j ≟ j
    ... | inl a = refl
    ... | inr ¬j with ¬j refl
    ... | ()
    
    f : Fin (suc n) → Fin n
    f x = proj n x 

    fromPigeon : ∃₂ λ i j → i ≢ j × f i ≡ f j 
    fromPigeon  = pigeonhole m≤sucm f 
    
    contra : fzero ≡ fsuc fzero
    contra with fromPigeon
    ... | i , j , i≠j , fi=fj = 
      fzero
              ≡⟨ sym (almost0i i≠j )⟩ 
      almost0 i
              ≡⟨  flattenval almost0 i ⟩ 
      lookup us i
              ≡⟨ sym (projβ (suc (suc m)) i (us {j})) ⟩ 
      ((proj (suc (suc m)) i) ·s us)
              ≡⟨ cong (λ x → x ·s us ) fi=fj ⟩ 
      ((proj (suc (suc m)) j) ·s us)
             ≡⟨ (projβ (suc (suc m)) j (us {j})) ⟩ 
      lookup us j
            ≡⟨ sym (flattenval almost0 j) ⟩ 
      almost0 j
            ≡⟨ (almost0j {j} ) ⟩ 
      refl
             
    bot : ⊥
    bot with contra
    bot | ()

notbool : (m : Model) → let module m = Model m in m.Tm ≡ (Fin 2) → ⊥
notbool m refl = notBoolModel2.bot _·_ K S Kβ Sβ 
  where
    open Model m

notfinite : (m : Model){n : ℕ} → let module m = Model m in m.Tm ≡ (Fin (suc (suc n))) → ⊥
notfinite record { Tm = .(Fin (suc (suc n))) ; _·_ = _·₁_ ; K = K₁ ; S = S₁ ; Kβ = Kβ₁ ; Sβ = Sβ₁ } {n} refl = 
  notFiniteModel2.bot n _·₁_ K₁ S₁ Kβ₁ Sβ₁ 
  
     