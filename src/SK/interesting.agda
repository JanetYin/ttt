module SK.interesting where
    
open import Lib 


⌜_⌝ : {n : ℕ} → Fin n → ℕ
⌜ fzero ⌝ = 0
⌜ fsuc x ⌝ = suc ⌜ x ⌝

⌞_⌟ : (n : ℕ) → Fin (suc n)
⌞ zero ⌟ = fzero
⌞ suc n ⌟ = fsuc ⌞ n ⌟

{-
safeSubtract : (n : ℕ) → ⦃ nonZero : 1 ≥ℕ n ⦄ → ℕ → ℕ
safeSubtract n m = n - m
-- Define a function to reverse the order in a Fin set

ind : {n : ℕ} → Fin (suc n) → Fin (suc n)
ind {n} x = ⌞ suc n - 1 - (⌜ x ⌝) ⌟

-- Example usage with specific redefinitions for clarity in how to use ind
example1 : ind {4} (fsuc fzero) ≡ fsuc (fsuc (fsuc fzero))
example1 = refl
-}

isEven isOdd : ℕ  → Set 
isEven zero = ⊤
isEven (suc x) = isOdd x

isOdd zero = ⊥
isOdd (suc x) = isEven x

2*Even : ∀ n → isEven (2 * n)
2*Even zero = tt
2*Even (suc n) =  subst isEven (sym (sucr+ (suc n) (n + 0))) (2*Even n)

pf1 : ∀ n → isEven (2 ^ suc n)
pf1 n = 2*Even (2 ^ n)

Even+ : ∀ m n → isEven m → isEven n → isEven (m + n)
Even+ zero zero x x₁ = tt
Even+ zero (suc n) x x₁ = x₁
Even+ (suc m) zero x x₁ = subst isOdd (sym (idr+ m)) x --(Even+ n 2 x₁ tt ) isEven (n+2)
Even+ (suc (suc m)) (suc (suc n)) x x₁ = subst isEven (sym (comm+ m (suc (suc n)))) (Even+ n m x₁ x) 

pf2-aux : ∀ {n} → {isOdd n} → isOdd (3 * n)
pf2-aux {(suc zero)} {e} = tt
pf2-aux {(suc (suc (suc n)))} {e} = subst isEven (sym (comm+ n (suc (suc (suc (n + suc (suc (suc (n + zero)))))))))  (subst isOdd (sym (assoc+ n (suc (suc (suc (n + zero)))) n)) (subst isOdd (sym (comm+ n (suc (suc (suc (n + zero + n)))))) (Even+ (n + zero + n) n (Even+ (n + zero) n (Even+ n zero e tt) e) e)))

pf2 : ∀ n → isOdd (3 ^ suc n) 
pf2 zero = tt
pf2 (suc n) = pf2-aux {(3 ^ n + (3 ^ n + (3 ^ n + zero)))} {pf2 n} 

numParity : ∀ n → isEven n → isOdd n → ⊥
numParity (suc n) e o = numParity n o e

pf3 : ∀{n m} → isEven n → isOdd m → n ≡ m → ⊥
pf3 {n} {.n} e o refl = numParity n e o

interesting : ∀ n m → 2 ^ suc n ≢ 3 ^ suc m
interesting n m = pf3 (pf1 n) (pf2 m)
