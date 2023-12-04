{- canvas kviz megbeszelese:
and = λ x y → if not y then false else x
and t t = if not t then false else t = if (if t then false else true) then false else t

-}

open import Lib

-- assoc mult oran

-- az osszeadasra mi teljesul definicio szerint?
-- zero + b = b                                   true ∧ b = b,   (a ∧ true ≡ a)
-- suc a + b = suc (a + b)

-- Q(b) := b ≡ b + zero
-- alapeset: Q(zero) = (zero ≡ zero + zero) = (zero ≡ zero) := refl
-- ind.eset: Q(n) -> Q(suc n)   (i.h. : n ≡ n + zero) -->  (suc n ≡ suc n + zero)
--                                                    (suc n ≡ suc (n + zero))
--    := cong suc i.h.

+-jobb-identitas : (b : ℕ) → b ≡ b + zero
+-jobb-identitas zero = refl
+-jobb-identitas (suc n) = cong suc (+-jobb-identitas n)

comm-seged : (a b : ℕ) → a + suc b ≡ suc a + b
comm-seged zero b = refl
comm-seged (suc a) b = cong suc (comm-seged a b)

-- t.i.  rogzitsuk b-t. indukcioval bizonyitsuk P(a) := (a + b ≡ b + a)
-- alapeset: P(zero) = (zero + b ≡ b + zero) = (b ≡ b + zero)   := +-jobb-identitas b
-- ind.eset: P(n)                   -> P(suc n)
--          i.h.:(n + b ≡ b + n)    -> (suc (n + b) ≡ b + suc n)
-- cong suc i.h. : suc (n + b) ≡ suc b + n
-- sym (comm-seged b n) : suc b + n ≡ b + suc n
-- trans (cong suc i.h.) (sym (comm-seged b n)) : suc (n + b) ≡ b + suc n

open import ea10 using (ind)

comm : (a b : ℕ) → a + b ≡ b + a
comm a b = ind (λ a → a + b ≡ b + a)
  (+-jobb-identitas b)
  (λ n ih → trans (cong suc ih) (sym (comm-seged b n)))
  a

-- (a+b)^2 = a^2+2ab+b^2

open import Lib.Nat.Properties

pl-biz : (a b c : ℕ) → a + (c + b) ≡ ((b + c) + 0) + a
pl-biz a b c =
-- a + (c + b)
  trans (comm+ a (c + b))
-- (c + b) + a
    (trans (cong (_+ a) (comm+ c b))
-- (b + c) + a
      (sym (cong (_+ a) (idr+ (b + c))))) 
-- b + c + 0 + a

pl-biz2 : (a : ℕ)(b : ℕ) → (a * b) * a ≡ b * (a * a)
pl-biz2 a b =
  (a * b) * a
                    ≡⟨ cong (_* a) (comm* a b) ⟩
  (b * a) * a
                    ≡⟨ ass* b a a ⟩
   b * (a * a)
                    ∎
   
-- egyenlosegi erveles

-- nem egyenlo ket dolog: ellenpelda

-- ((n : ℕ) → (P n ⊎ Q n)  ↔  (∀ n → P n) ⊎ (∀ n → Q n)) → ⊥

P : ℕ → Set
P 0 = ⊤
P 5 = ⊥
P _ = ⊤

0≠5' 0≠5 : ¬ (_≡_ {A = ℕ} 0 5)
0≠5 0=5 = subst P 0=5 tt
0≠5' ()

⊤≠⊥ : ¬ (⊤ ≡ ⊥)
⊤≠⊥ e = subst (λ X → X) e tt

hf : inl tt ≡ inr tt → ⊥
hf ()

nem : ((x y : ⊤ ⊎ ⊤) → x ≡ y) → ⊥
nem h = hf (h (inl tt) (inr tt))

⊤≠⊤+⊤ : ¬ (⊤ ≡ (⊤ ⊎ ⊤))
⊤≠⊤+⊤ e = nem (subst (λ X → (x y : X) → x ≡ y) e (λ _ _ → refl))

-- refl,sym,trans,cong,subst(transport)

-- kov. ora 4 perccel rovidebb
