{-# OPTIONS --without-K #-}

module SK-Confl where

open import Agda.Builtin.Sigma

infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A λ _ → B

infixl 10 _·_
data Tm : Set where
  K S : Tm
  _·_ : Tm → Tm → Tm

private variable
 x x′ y y′ z z′ : Tm

infix 4 _↝_
data _↝_ : Tm → Tm → Set where
  K : K ↝ K
  S : S ↝ S
  _·_ : (x ↝ x′) → (y ↝ y′) → (x · y ↝ x′ · y′)
  K-β : (x ↝ x′) → (K · x · y ↝ x′)
  S-β : (x ↝ x′) → (y ↝ y′) → (z ↝ z′) → (S · x · y · z ↝ x′ · z′ · (y′ · z′))

infix 4 _↝*_
infixr 9 _∙_
data _↝*_ : Tm → Tm → Set where
  refl : x ↝* x
  _∙_ : (x ↝ y) → (y ↝* z) → (x ↝* z)

step : Tm → Tm
step K = K
step S = S
step (K · x · y) = step x
step (S · x · y · z) = step x · step z · (step y · step z)
{-# CATCHALL #-}
step (x · y) = step x · step y

↝-step : (x ↝ y) → (y ↝ step x)
↝-step K = K
↝-step S = S
↝-step (_·_ {x = K} x↝ y↝) = ↝-step x↝ · ↝-step y↝
↝-step (_·_ {x = S} x↝ y↝) = ↝-step x↝ · ↝-step y↝
↝-step (_·_ {x = K · x} (K · x↝) y↝) = K-β (↝-step x↝)
↝-step (_·_ {x = S · x} x↝ y↝) = ↝-step x↝ · ↝-step y↝
↝-step (_·_ {x = K · x · y} x↝ z↝) = ↝-step x↝ · ↝-step z↝
↝-step (_·_ {x = S · x · y} (S · x↝ · y↝) z↝) =
  S-β (↝-step x↝) (↝-step y↝) (↝-step z↝)
↝-step (_·_ {x = x · y · z · t} x↝ u↝) = ↝-step x↝ · ↝-step u↝
↝-step (K-β x↝) = ↝-step x↝
↝-step (S-β x↝ y↝ z↝) = ↝-step x↝ · ↝-step z↝ · (↝-step y↝ · ↝-step z↝)

↝-confl : (x ↝ y) → (x ↝ y′) → Σ Tm (λ z → y ↝ z × y′ ↝ z)
↝-confl {x} x↝ x↝′ = (step x , ↝-step x↝ , ↝-step x↝′)

strip :  (x ↝ y)  → x ↝* y′ → Σ Tm (λ z → y ↝* z × y′ ↝ z) 
strip x↝ refl = _ , refl , x↝
strip x↝ (x↝' ∙ x↝*) with strip (fst (snd (↝-confl x↝' x↝))) x↝* 
... | z , s↝* , y'↝ = z , ((snd (snd (↝-confl x↝' x↝))) ∙ s↝*) , y'↝

↝*-confl : (x ↝* y) → (x ↝* y′) → Σ Tm (λ z → y ↝* z × y′ ↝* z)
↝*-confl refl x↝*' = _ , (x↝*' , refl)
↝*-confl (x↝ ∙ x↝*) refl = _ , (refl , x↝ ∙ x↝*)
↝*-confl (x↝ ∙ y↝*) (x↝' ∙ y↝*') with strip x↝ (x↝' ∙ y↝*')
... | z , y₁↝* , y'↝ with ↝*-confl y↝* y₁↝*  
... | z' , y↝*' , z↝* = z' , (y↝*' , (y'↝ ∙ z↝*)) 