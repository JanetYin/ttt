-- proofs of simple properties of ℕ by induction
-- ℕ form a commutative monoid
-- prove some equations using the comm.monoid laws

open import Lib

idl : (n : ℕ) → 0 + n ≡ n
idl n = refl
 
idr : (n : ℕ) → n + 0 ≡ n
idr zero    = refl
idr (suc n) = cong suc (idr n)

ass : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass zero    n o = refl
ass (suc m) n o = cong suc (ass m n o)

{-
n + suc m ≡ suc n + m
suc m = 0 + suc m ≡ suc 0 + m = suc (0 + m) = suc m
suc (suc m) = suc (0 + suc m) = 1 + suc m ≡ suc 1 + m = suc (suc 0 + m) = suc (suc m)
-}
comm-helper : (m n : ℕ) → n + suc m ≡ suc n + m
comm-helper m zero = refl
comm-helper m (suc n) = cong suc (comm-helper m n)

comm : (m n : ℕ) → m + n ≡ n + m
comm zero    n = sym (idr n)
comm (suc m) n = trans (cong suc (comm m n)) (sym (comm-helper m n))
-- cong suc (comm m n)   : suc (m + n) ≡ suc (n + m)
-- sym (comm-helper m n) : suc (n + m) ≡ n + suc m

record Monoid (Car : Set) : Set where -- egysegelemes felcsoport
  field      -- Car is the carrier
    unit : Car
    op   : Car → Car → Car
    left-unit : (c : Car) → op unit c ≡ c
    right-unit : (c : Car) → op c unit ≡ c
    assoc : (c c' c'' : Car) → op (op c c') c'' ≡ op c (op c' c'')
open Monoid

ℕm : Monoid ℕ
unit ℕm = zero
op ℕm = _+_
left-unit ℕm = idl
right-unit ℕm = idr
assoc ℕm = ass

Trm : Monoid ⊤ -- terminal monoid
unit Trm = _
op Trm = _
left-unit Trm = λ _ → refl
right-unit Trm = λ _ → refl
assoc Trm = λ _ _ _ → refl

noMonoidOn⊥ : Monoid ⊥ → ⊥
noMonoidOn⊥ M = unit M

idr-L : {A : Set}(as : List A) → as List.++ [] ≡ as
idr-L []       = refl
idr-L (a ∷ as) = cong (a ∷_) (idr-L as)

ass-L : {A : Set}(m n o : List A) → (m List.++ n) List.++ o ≡ m List.++ (n List.++ o)
ass-L []    n o = refl
ass-L (a ∷ m) n o = cong (a ∷_) (ass-L m n o)

L : (A : Set) → Monoid (List A)
unit (L A) = []
op (L A) = List._++_
left-unit (L A) = λ _ → refl
right-unit (L A) = idr-L
assoc (L A) = ass-L

record CommMonoid (A : Set) : Set where
  field
    Mon : Monoid A
    commut : (c c' : A) → op Mon c c' ≡ op Mon c' c
open CommMonoid

ℕcm : CommMonoid ℕ
Mon ℕcm = ℕm
commut ℕcm = comm

listNotCommMon : ¬ ((A : Set) → CommMonoid (List A))
listNotCommMon H = {!comm1 (true ∷ []) (false ∷ [])!} -- TODO
  where
    op' : List Bool → List Bool → List Bool
    op' = op (Mon (H Bool))
    comm1 : (c c' : List Bool) → op' c c' ≡ op' c' c
    comm1 = commut (H Bool)
    
{-
listNotCommMon : ¬ ((A : Set) → Σ CommMonoid λ M → Car (Mon M) ≡ List A)
listNotCommMon H = {!cast!}
  where
    comm0 : (c c' : Car (Mon (fst (H Bool)))) →
      op (Mon (fst (H Bool))) c c' ≡ op (Mon (fst (H Bool))) c' c
    comm0 = commut (fst (H Bool))
    op' : List Bool → List Bool → List Bool
    op' xs ys = cast (snd (H Bool))
      (op (Mon (fst (H Bool)))
        (cast (sym (snd (H Bool))) xs)
        (cast (sym (snd (H Bool))) ys))
    comm1 : (c c' : List Bool) → c List.++ c' ≡ c' List.++ c
    comm1 = {!snd (H Bool)!}
-}

eq' : (a b c : ℕ) → (a + ((b + (a + 0)) + c)) ≡ a + a + b + c
eq' a b c = trans
  (cong (λ z → a + (b + z + c)) (idr a))
  (trans (cong (λ z → a + (z + c)) (comm b a))
  (trans (sym (ass a (a + b) c))
  (cong (_+ c) (sym (ass a a b)))))

module _ (C : Set)(M : CommMonoid C)(a b c : C)
  where
  _+'_ = op (Mon M)
  infixl 6 _+'_
  zer = unit (Mon M)

  eq'' : (a +' ((b +' (a +' zer)) +' c)) ≡ a +' a +' b +' c
  eq'' = trans
    (cong (λ z → a +' (b +' z +' c)) (right-unit (Mon M) a))
    (trans (cong (λ z → a +' (z +' c)) (commut M b a))
    (trans (sym (assoc (Mon M) a (a +' b) c))
    (cong (_+' c) (sym (assoc (Mon M) a a b)))))

F : (A : Set) → Monoid (A → A)
unit (F A) = λ a → a
op (F A) = _∘_
left-unit (F A) = λ _ → refl
right-unit (F A) = λ _ → refl
assoc (F A) = λ _ _ _ → refl
