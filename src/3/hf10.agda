module hf10 where

open import Lib hiding (dist*+; nullr*; idl*; idr*; ass*; comm*)

dist*+ : (m n o : ℕ) → m * (n + o) ≡ m * n + m * o
dist*+ = {!   !}

nulll* : (n : ℕ) → 0 * n ≡ 0
nulll* = {!   !}

nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* = {!   !}

idl* : (n : ℕ) → 1 * n ≡ n
idl* = {!   !}

idr* : (n : ℕ) → n * 1 ≡ n
idr* = {!   !}

ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* = {!   !}

comm*-helper : (n m : ℕ) → n * suc m ≡ n + n * m
comm*-helper = {!!}

comm* : (m n : ℕ) → m * n ≡ n * m
comm* = {!!}

--------------------------------------------------------

2n : (n : ℕ) → 2 * n ≡ n + n
2n = {!   !}

2n' : (n : ℕ) → n * 2 ≡ n + n
2n' = {!   !}

very-comm : (a b c d : ℕ) → (a * b) + (c * d) ≡ (d * c) + (b * a)
very-comm = {!  !}

-- Hosszabb feladat
sumSq : (a b : ℕ) → (a + b) * (a + b) ≡ a * a + 2 * a * b + b * b
sumSq = {!   !}