open import lib hiding (_⊎_; inl; inr; case; ⊥; exfalso)

-- ez az ora 4 perccel rovidebb

-- kviz

-- lambda kalkulus es veges tipusok

-- eddig: →, ℕ, {A : Set} →

-- lambda kalkulus, a termek kornyezetben, β, (λ x → (λ y → x + y)) y, α, η

-- kombinator logika

K : {A B : Set} → A → B → A
K = λ a b → a

S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S = λ f g a → f a (g a)

-- comnbinator conversion: (λ x → t) is converted by looking at t (which does not contain λ)
-- convert _∘_ into combinatory terms

-- ⊎, CustRef, OrdNum, ugyanaz a szam; ∪ vs. ⊎

-- ×, curry, uncurry, izomorfizmus

-- ⊤, ⊥, Bool=⊤+⊤

-- finite type isos




