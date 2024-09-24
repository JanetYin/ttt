module SK.php where

open import Lib hiding (_<_)

private
  variable
    a b c ℓ₁ ℓ₂ p w : Level
    A : Set a
    B : Set b
    C : Set c
    P : Set p

REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ

-- Homogeneous binary relations
Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Rel A ℓ = REL A A ℓ

data _≤_ : Rel ℕ 0ℓ  where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_<_ : Rel ℕ 0ℓ 
m < n = suc m ≤ n

<+k : ∀ {n k } → n ≤ (n + k) 
<+k {zero} {k} = z≤n
<+k {suc n} {k} = s≤s <+k

∃₂ : ∀ {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b 

any?' : ∀ {n p} {P : Fin n → Set p} → Decidable P → Dec (∃ P)
any?' {zero} {_} {P} P? = inr (λ {()})
any?' {suc n} {p} {P} (DecProof P?) with P? fzero | any?' {n} {p} {λ i → P (fsuc i)} (DecProof λ x → P? (fsuc x))
... | inl P₀  | _ = inl (_ , P₀)
... | inr ¬P₀ | inl (i , P₁₊ᵢ) = inl ((fsuc i) , P₁₊ᵢ)
... | inr ¬P₀ | inr ¬P₁₊ᵢ = inr (λ {(fzero ,  P₀) → ¬P₀ P₀
                                  ; (fsuc f , P₁₊ᵢ) → ¬P₁₊ᵢ (_ , P₁₊ᵢ)})

punchOut : ∀ {m} {i j : Fin (suc m)} → i ≢ j → Fin m
punchOut {_}     {fzero}   {fzero}  i≢j = exfalso (i≢j refl)
punchOut {_}     {fzero}   {fsuc j} _   = j
punchOut {suc m} {fsuc i}  {fzero}  _   = fzero
punchOut {suc m} {fsuc i}  {fsuc j} i≢j = fsuc (punchOut (i≢j ∘ cong fsuc)) 

punchOut-injective : ∀ {m} {i j k : Fin (suc m)}
                     (i≢j : i ≢ j) (i≢k : i ≢ k) →
                     punchOut i≢j ≡ punchOut i≢k → j ≡ k
punchOut-injective {_}     {fzero}   {fzero}  {_}     0≢0 _   _     = contradiction refl 0≢0
punchOut-injective {_}     {fzero}   {_}     {fzero}  _   0≢0 _     = contradiction refl 0≢0
punchOut-injective {_}     {fzero}   {fsuc j} {fsuc k} _   _   pⱼ≡pₖ = cong fsuc pⱼ≡pₖ
punchOut-injective {suc n} {fsuc i}  {fzero}  {fzero}  _   _    _    = refl
punchOut-injective {suc n} {fsuc i}  {fsuc j} {fsuc k} i≢j i≢k pⱼ≡pₖ =
  cong fsuc (punchOut-injective (i≢j ∘ cong fsuc) (i≢k ∘ cong fsuc) {!   !} )--(fsuc-injective pⱼ≡pₖ))
  
pigeonhole : ∀ {m n} → m < n → (f : Fin n → Fin m) →
             ∃₂ λ i j → i ≢ j × f i ≡ f j
pigeonhole (s≤s z≤n) f = contradiction (f fzero) λ()
pigeonhole (s≤s (s≤s m≤n)) f with any?' (DecProof (λ x →  (f fzero) ≟ (f (fsuc x))))
... | inl (j , f₀≡fⱼ) = fzero , ((fsuc j) , ((λ {()}) , f₀≡fⱼ))
... | inr f₀≢fₖ with pigeonhole (s≤s m≤n) (λ j → punchOut (f₀≢fₖ  ∘ (j ,_ )) )
... | i , j , i≢j  , fᵢ≡fⱼ = fsuc i , (fsuc j , (i≢j ∘ fsuc-injective , punchOut-injective (f₀≢fₖ  ∘  ((i ,_))) _ fᵢ≡fⱼ))      

lower₁ : ∀ {n} → (i : Fin (suc n)) → (n ≢ toℕ i) → Fin n
lower₁ {zero} fzero ne = exfalso (ne refl)
lower₁ {suc n} fzero _ = fzero
lower₁ {suc n} (fsuc i) ne = fsuc (lower₁ i λ x → ne (cong suc x))

replicate : ∀ {a n} {A : Set a} → A → Vec A n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

repeat : ∀ {a}{A : Set a} → A → (m : ℕ) → Vec A m
repeat tm zero = []
repeat tm (suc t) = tm ∷ (repeat tm t)

_++_ : ∀ {a m n} {A : Set a} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)