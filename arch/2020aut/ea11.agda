module lec.ea11 where

open import lib

{-
Kvíz kérdések:
-----------------

(R : ℕ → ℕ → Set) → 

  (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) → Σ ℕ (λ x → R x x))   NINCS

_<_     (0 , (1 , ...))              
                  ^ : 0 < 1 

  (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) ← Σ ℕ (λ x → R x x))   VAN
-}

f3 : (R : ℕ → ℕ → Set) → 
  (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) → Σ ℕ (λ x → R x x)) --  NINCS
f3 R (x , y , r) = 0 , {!!}

ellenR : ℕ → ℕ → Set
ellenR zero (suc zero) = ⊤
ellenR _    _          = ⊥

ellenRtul : (x : ℕ) → ¬ (ellenR x x)
ellenRtul zero = λ x → x
ellenRtul (suc x) = λ x → x

¬f3 : ¬ ((R : ℕ → ℕ → Set) → (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) → Σ ℕ (λ x → R x x)))
¬f3 w = ellenRtul (proj₁ (w ellenR (0 , (1 , tt)))) (proj₂ (w ellenR (0 , (1 , tt))))

f4 : (R : ℕ → ℕ → Set) → 
   (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) ← Σ ℕ (λ x → R x x)) 
f4 R (x , r) = x , x , r

{-
   A × (B × C) ≅ (A × B) × C
   Σ A (λ x → Σ (B x) (C x)) ≅ Σ (Σ A B) (λ w → C (proj₁ w) (proj₂ w))

  (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) → Σ (ℕ × ℕ) (λ w → R (proj₁ w) (proj₂ w)))
  (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) ← Σ (ℕ × ℕ) (λ w → R (proj₁ w) (proj₂ w)))
  
  Σ ℕ (λ x → R x x → R (suc x) (suc x))

    R 0 0 := ⊤
    R _ _ := ⊥

  (R zero zero → R (suc zero) (suc zero))

    R 0 0 := ⊤
    R _ _ := ⊥



Σ Set (λ A → ¬ A)  <- létezik egy állítás, ami hamis
-}

f1 : Σ Set (λ A → ⊥)
f1 = ⊥ , {!!}  -- most már biztos nincs eleme
¬f1 : ¬ (Σ Set (λ A → ⊥))
¬f1 = proj₂

Eqℕ : ℕ → ℕ → Set
Eqℕ zero    zero    = ⊤
Eqℕ (suc _) zero    = ⊥
Eqℕ zero    (suc _) = ⊥
Eqℕ (suc x) (suc y) = Eqℕ x y

{-
() : Σ Set (λ A → ⊥)	= Set × ⊥   <- létezik egy állítás, hogy hamis = van egy állítás és hamis

Σ ℕ (λ x → Eq ℕ x x → ⊥)    <- van olyan szám, amely nem egyenlő önmagával
Σ ℕ (λ x → Eqℕ x (suc x) → Eqℕ (suc x) x) <- ha x=1+x, akkor 1+x=x.
-}
f2 : Σ ℕ (λ x → Eqℕ x zero → ⊥) --   <- van olyan szám, amely nem egyenlő 0-val
f2 = 1 , λ b → b
{-
Σ (ℕ → ℕ → Set) (λ R → (R zero zero ↔ R (suc zero) (suc zero)))  <- R x y := ⊤

egyenletek használata
decidable equality (pattern matching)
<=

-}

-- szokásos elsőrendű logikai bevezető feladat, kocsmáról

-- kitero:
ilyenNincs : (bs : ℕ → Bool) →
  (Σ ℕ λ i → Eq Bool (bs i) true) ⊎ ¬ (Σ ℕ λ i → Eq Bool (bs i) true)
ilyenNincs bs = {!!}
-- bs 0, bs 1, bs 2, ... : Bool

¬¬lem : (A : Set) → ¬ ¬ (A ⊎ ¬ A)
¬¬lem = λ A w → w (inj₂ λ a → w (inj₁ a))

-- minden nemüres kocsmában van egy vendég, aki ha iszik, akkor mindenki iszik
kocsmatetel : 
  (Vendeg : Set)
  (Iszik  : Vendeg → Set)
  (valaki : Vendeg)
  (lem    : (A : Set) → A ⊎ ¬ A) →      -- A ⊎ ¬ A = A eldönthető,  lem:minden állítás eldönthető

  Σ Vendeg λ v → Iszik v → (w : Vendeg) → Iszik w
--∃v . Iszik(v) ⇒ ∀ w . Iszik(w)

kocsmatetel Vendeg Iszik valaki lem = case
  (lem (Σ Vendeg (λ v → ¬ Iszik v)))
  (λ w → proj₁ w , λ i → exfalso (proj₂ w i))
  (λ w → valaki , λ _ u → case
    (lem (Iszik u))
    (λ iu → iu)
    λ niu → exfalso (w (u , niu)))

-- elsőrendű logika Agdában
