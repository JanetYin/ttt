module ea05 where

open import lib

{- kviz

f , g : ⊤ → ⊤
f =(→ η) (λ x → f x) =(⊤ η) (λ x → tt) =(⊤ η) (λ x → g x) =(→ η) g

(λ x → tt) : ⊤ → ⊤
(λ x → x)  : ⊤ → ⊤
-}

-- cukorka
fg : (f g : ⊤ → ⊤) → f ≡ g
fg f g = refl

-- (λ x → if x then x else x) = (λ x → if x then true else false)

-- (1+n)*2+1 = 2 + n*2 + 1 = n*2 + 3

{-
   tipus            bevezeto         eliminacios
                    (a Goal az ez)   (a lyukba beirtam hogy t, es ennek a tipusa ez (Have))
   ---------------------------------------------------------------------------------
   ⊥                                 exfalso t
   ⊤                tt
   A ⊎ B            inl ?            case t ? ?
                    inr ?
   A × B            ? , ?            fst t
                                     snd t
   A → B            λ x → ?          t ?
   Bool             true             if t then ? else ?
                    false
   ℕ                zero             iteℕ ? ? t
                    suc ?
   ----------------------------------------------------------------------------------
   ha van egy olyan feltelem, ami = Goal-al, akkor azt kozvetlenul hasznalhatom
-}
pl : (A : Set) → ((A ⊎ (A → ⊥)) → ⊥) → ⊥
pl A = λ x → x (inr λ y → x (inl y))

-- ez az eloadas 10 perccel rovidebb

-- Vec A : ℕ → Set, List : Set → Set, polymorphism is special case

infixr 5 _∷_

data List (A : Set) : Set where  -- data List A = [] | A ∷ List A
  []  : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where -- ℕ-al indexelt tipus
  []  : Vec A 0
  _∷_ : A → {n : ℕ} → Vec A n → Vec A (suc n)

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

zeroes-l : ℕ → List ℕ
zeroes-l 0 = []
zeroes-l (suc n) = 0 ∷ zeroes-l n

zeroes-v : (n : ℕ) → Vec ℕ n   -- zeroes-v 0 : Vec ℕ 0,    zeroes-v 3 : (Vec ℕ 3)
zeroes-v 0 = []
zeroes-v (suc n) = 0 ∷ zeroes-v n

_++l_ : List ℕ → List ℕ → List ℕ
[]       ++l ys = ys
(x ∷ xs) ++l ys = x ∷ (xs ++l ys)

-- implicit parameter
_++v_ : {m n : ℕ} → Vec ℕ m → Vec ℕ n → Vec ℕ (m + n)
[]       ++v ys = ys
(x ∷ xs) ++v ys = x ∷ (xs ++v ys)

_!!l_ : {A : Set} → List A → ℕ → Maybe A
[] !!l n = Nothing
(x ∷ xs) !!l zero = Just x
(x ∷ xs) !!l suc n = xs !!l n

_!!0 : {A : Set} → {n : ℕ} → Vec A (1 + n) → A
(x ∷ xs) !!0 = x

Fin' : ℕ → Set
Fin' zero = ⊥
Fin' (suc n) = Maybe (Fin' n)
-- Fin' (suc n) = Fin' n ⊎ ⊤
-- Fin' 2 = Maybe (Maybe ⊥) = {Nothing, Just Nothing}

data Fin : ℕ → Set where -- veges halmazok, Fin 3 = 3-elemu tipus, Fin 2 = 2-elemu tipus, Fin 0 = 0-elemu tipus
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

f01 : Fin 1
f01 = zero {0}

f02 f12 : Fin 2
f02 = zero {1}
f12 = suc {1} (zero {0})

f03 f13 f23 : Fin 3
f03 = zero {2}
f13 = suc zero
f23 = suc (suc zero)

_!!v_ : {A : Set} → {n : ℕ} → Vec A n → Fin n → A
(x ∷ xs) !!v zero = x
(x ∷ xs) !!v suc n = xs !!v n 

-- kovetkezo ora 10 perccel lesz rovidebb

-- Π types, szabalyok, special case simply typed

-- Σ types, szabalyok, FlexVec

{-
ez jovo oran lesz:

    Π     Σ
   / \   / \
  /   \ /   \
 →     ×     ⊎
-}
