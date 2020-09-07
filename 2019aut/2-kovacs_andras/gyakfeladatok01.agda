
module gyakfeladatok01 where

open import lib

-- Logikai ekvivalencia: lib-ben definiált, A ↔ B = (A → B) × (B → A)
-- példa használatra:
currying : (X × Y → Z) ↔ (X → Y → Z)
currying = (λ f x y → f (x , y)) , (λ f p → f (proj₁ p) (proj₂ p))

-- Algebrai ekvivalenciák alaptípusokra, lásd előadásjegyzet
------------------------------------------------------------

-- szorzat
×assoc : (X × Y × Z) ↔ ((X × Y) × Z)
×assoc = {!!}

×unit : (⊤ × X) ↔ X
×unit = {!!}

×commutative : (X × Y) ↔ (Y × X)
×commutative = {!!}

×null : (X × ⊥) ↔ ⊥
×null = {!!}

-- összeg
⊎assoc : (X ⊎ Y ⊎ Z) ↔ ((X ⊎ Y) ⊎ Z)
⊎assoc = {!!}

⊎unit : (⊥ ⊎ X) ↔ X
⊎unit = {!!}

⊎commutative : (X ⊎ Y) ↔ (Y ⊎ X)
⊎commutative = {!!}

-- disztribúció
distrib : ((X ⊎ Y) × Z) ↔ ((X × Z) ⊎ (Y × Z))
distrib = {!!}

-- függvények
⊎→ : ((X ⊎ Y) → Z) ↔ ((X → Z) × (Y → Z))
⊎→ = {!!}

×→ : ((X × Y) → Z) ↔ (X → (Y → Z))
×→ = {!!}

⊥→ : (⊥ → X) ↔ ⊤
⊥→ = {!!}

⊤→ : (⊤ → X) ↔ X
⊤→ = {!!}
