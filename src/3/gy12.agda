module gy12 where

open import Lib

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

sucinj : (m n : ℕ) → ℕ.suc m ≡ suc n → m ≡ n
sucinj = {!!}

-- prove it without pattern matching on e! (hint: use pred')
sucinj' : (m n : ℕ) → ℕ.suc m ≡ suc n → m ≡ n
sucinj' m n e = {!!}

-- Nyilván ez más típusokon is működik, azokról majd következő órán lesz szó.

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

true≠false : true ≢ false
true≠false = {!!}

-- prove this without pattern matching in this function on e! (use subst!)
true≠false' : true ≢ false
true≠false' e = {!!}

zero≠sucn : {n : ℕ} → zero ≢ ℕ.suc n
zero≠sucn = {!!}

zero≠sucn' : {n : ℕ} → zero ≢ ℕ.suc n
zero≠sucn' = {!!}

-- Nyilván ez más típusokon is működik, azokról majd következő órán lesz szó.

--------------------------------------------------------
-- Negáltas bizonyítások, elsőrendű logika után szabadon
--------------------------------------------------------

p9' : 0 ≢ the ℕ 1
p9' = {!   !}

p9 : 2 * 2 ≢ 5 * 1
p9 = {!   !}

-- Egyszerűbb, amikor mondani kell egy ellenpéldát:
p10 : ¬ ((n : ℕ) → n + 2 ≡ n + 1)
p10 = {!   !}

-- ...mintsem bizonyítani, hogy ez a kettő sosem lesz egyenlő:
p11 : (n : ℕ) → n + 2 ≢ n + 1
p11 = {!   !}

-----------------------------------------------
-- Nem léteziket más dolog bizonyítani.
p12 : ¬ Σ ℕ (λ n → n + n ≡ 3)
p12 = {!   !}

p13 : ¬ Σ ℕ (λ n → ∀ x → x + suc n ≡ x)
p13 = {!   !}

p14 : ¬ Σ ℕ (λ n → n + n ≢ 2 * n) 
p14 = {!   !}

----------------------------

-- Nehezebb eset, de példát mondani továbbra is egyszerű.
p15 : ¬ ((n k : ℕ) → 2 ^' suc n ≡ 3 ^' suc k)
p15 = {!   !}

-- Na de ha minden n,k-ra kell bizonyítani...!
p16 : (n k : ℕ) → 2 ^' suc n ≢ 3 ^' suc k
p16 = {!   !}