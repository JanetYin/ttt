module gy12 where

open import Lib

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

sucinj : (m n : ℕ) → ℕ.suc m ≡ suc n → m ≡ n
sucinj _ _ refl = refl

g : ℕ → ℕ
g zero = 32487
g (suc n) = n

-- prove it without pattern matching on e!
sucinj' : (m n : ℕ) → ℕ.suc m ≡ suc n → m ≡ n
sucinj' m n e = cong g e

-- Nyilván ez más típusokon is működik, azokról majd következő órán lesz szó.

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

-- \==n : ≢
true≠false : true ≢ false
true≠false ()

-- prove this without pattern matching in this function on e! (use subst!)
true≠false' : true ≢ false
true≠false' e = subst P e tt where
  P : Bool → Set
  P false = ⊥
  P true = ⊤

zero≠sucn : {n : ℕ} → zero ≢ ℕ.suc n
zero≠sucn ()

zero≠sucn' : {n : ℕ} → zero ≢ ℕ.suc n
zero≠sucn' e = subst P e tt where
  P : ℕ → Set
  P zero = ⊤
  P (suc _) = ⊥

-- Nyilván ez más típusokon is működik, azokról majd következő órán lesz szó.

--------------------------------------------------------
-- Negáltas bizonyítások, elsőrendű logika után szabadon
--------------------------------------------------------

p9' : 0 ≢ the ℕ 1
p9' ()

p9 : 2 * 2 ≢ 5 * 1
p9 ()

-- Egyszerűbb, amikor mondani kell egy ellenpéldát:
p10 : ¬ ((n : ℕ) → n + 2 ≡ n + 1)
p10 f = 2≢1 (f 0) where
  2≢1 : the ℕ 2 ≢ 1
  2≢1 ()

p10' : ¬ ((n : ℕ) → n + 2 ≡ n + 1)
p10' f with f 0
... | ()

-- ...mintsem bizonyítani, hogy ez a kettő sosem lesz egyenlő:
p11 : (n : ℕ) → n + 3 ≢ n + 1
p11 (suc n) e = p11 n (suc-injective e)

p11' : (n : ℕ) → n + 3 ≢ n + 1
p11' n e with trans (comm+ 3 n) (trans e (comm+ n 1))
... | ()

-----------------------------------------------
-- Nem léteziket más dolog bizonyítani.
p12 : ¬ Σ ℕ (λ n → n + n ≡ 3)
p12 (suc (suc (suc zero)) , ())
p12 (suc (suc (suc (suc n))) , ())

-- \all = \forall = ∀
{-
p12' : ¬ Σ ℕ (λ n → n + n ≡ 3)
p12' (n , e) = {! h   !} where
  h : (∀ k → k + k ≢ 3) → ¬ Σ ℕ (λ n → n + n ≡ 3)
  h f (n , e) = f n e
  t : ∀ k → k + k ≢ 3
  t (suc k) e = ?
-}

p13 : ¬ Σ ℕ (λ n → ∀ x → x + suc n ≡ x)
p13 (n , e) with e 0
... | ()

p14 : ¬ Σ ℕ (λ n → n + n ≢ 2 * n) 
p14 (n , e) = e (cong (n +_) (sym (idr+ n)))

----------------------------

-- Nehezebb eset, de példát mondani továbbra is egyszerű.
p15 : ¬ ((n k : ℕ) → 2 ^' suc n ≡ 3 ^' suc k)
p15 = {!   !}

-- Na de ha minden n,k-ra kell bizonyítani...!
p16 : (n k : ℕ) → 2 ^' suc n ≢ 3 ^' suc k
p16 = {!   !}