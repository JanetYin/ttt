module t4.hw03 where
open import lib

--------------------------------------------------------------------------------

-- Define a function `apply1or3`. The application `apply1or3 b f x` should apply
-- the function `f` to the argument `x`, once if the boolean `b` is true, or
-- three times otherwise.
apply1or3 : {A : Type} → Bool → (A → A) → A → A
apply1or3 = {!!}

-- Tests:
-- apply1or3Test₁ : apply1or3 true  (λ n → n + 1) 10 ≡ 11; apply1or3Test₁ = refl
-- apply1or3Test₂ : apply1or3 false (λ n → n + 1) 10 ≡ 13; apply1or3Test₂ = refl
-- apply1or3Test₃ : apply1or3 true  (λ n → n * 2) 10 ≡ 20; apply1or3Test₃ = refl
-- apply1or3Test₄ : apply1or3 false (λ n → n * 2) 10 ≡ 80; apply1or3Test₄ = refl

--------------------------------------------------------------------------------

compose3 : {A B C D : Type} → (C → D) → (B → C) → (A → B) → (A → D)
compose3 = {!!}

-- Tests:
-- compose3Test₁ : compose3 (λ n → n + 1) (λ n → n * 2) (λ n → n + 1) 10 ≡ 23; compose3Test₁ = refl
-- compose3Test₂ : compose3 (λ n → n * 2) (λ n → n + 1) (λ n → n * 2) 10 ≡ 42; compose3Test₂ = refl

--------------------------------------------------------------------------------

-- Define a function `order-3` with the following type:
order-3 : {A B C D : Type} → ((A → C) → A → D) → (A → B) → A → (B → C) → D
order-3 = {!!}

--------------------------------------------------------------------------------

-- Define the uncurried or function.
or : Bool × Bool → Bool
or (x , y) = {!!}

-- Tests:
-- or-test₁ : or (true , true)   ≡ true;  or-test₁ = refl
-- or-test₂ : or (true , false)  ≡ true;  or-test₂ = refl
-- or-test₃ : or (false , true)  ≡ true;  or-test₃ = refl
-- or-test₄ : or (false , false) ≡ false; or-test₄ = refl

--------------------------------------------------------------------------------

-- Define functions perm₁ and perm₂ that permute the elements of a ternary product.
perm₁ : {A B C : Type} → A × B × C → B × A × C
perm₁ = {!!}

perm₂ : {A B C : Type} → A × B × C → A × C × B
perm₂ = {!!}

--------------------------------------------------------------------------------
