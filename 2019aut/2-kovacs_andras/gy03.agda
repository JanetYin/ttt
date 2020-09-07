
open import lib

-- Gyakorlás: _×_, _⊎_, ⊤, ⊥, ℕ
------------------------------------------------------------

-- lib-ből van olyan: X, Y, Z absztrakt típus

-- emlékeztető:
-- proj₁ : A × B → A      -- első mező
-- proj₂ : A × B → B      -- második mező
-- _,_   : A → B → A × B  -- párképzés

-- függvényt írni, egymásba ágyazott pár típus
-- X × (Y × Z) az input
-- output: (X × Y) × Z
f1 : X × (Y × Z) → (X × Y) × Z
f1 = -- λ p → ?       -- C-c-C-r : finomítás
     -- λ p → ? , ?
     -- λ p → (? , ?) , ?
  λ p → (proj₁ p , proj₁ (proj₂ p)) , proj₂ (proj₂ p)


  -- alsó index: \_
  -- λ ugyanaz, mint \ Haskell-ben.

-- feladatok
f2 : X × (Y × (Z × X)) → Z
f2 = λ p → proj₁ (proj₂ (proj₂ p))

f3 : X → X × X × X × X
f3 = λ x → x , (x , (x , x))

-- elemek sorrendjének megfordítása
f4 : X × Y × Z → Z × Y × X
f4 = λ p →
  proj₂ (proj₂ p) ,
  (proj₁ (proj₂ p) , proj₁ p)  -- C-c-C-a

f5 : (X → Y × Z) → (X → Y) × (X → Z)
f5 = λ f → (λ x → proj₁ (f x))
         , (λ x → proj₂ (f x))

-- f5 inverz függvénye
-- (f5-f6 izomorfizmus/bijekció)
f6 : (X → Y) × (X → Z) → (X → Y × Z)
f6 = λ p → λ x → proj₁ p x , proj₂ p x

-- A × B Haskell-ben: (a, b)
-- proj₁ : fst
-- proj₂ : snd
-- _,_   : (,)

-- (A → B) Haskell-ben: a -> b
-- λ x → t  : \x → t           -- anonim függvény
-- f x      : f x

-- A ⊎ B Haskell-ben: Either a b
-- data Either a b = Left a | Right b
-- inj₁ : Left
-- inj₂ : Right
-- case : either

-- összeg típus: A ⊎ B értékei vagy A típusú értéket
-- tartalmaznak, vagy B típusú értéket.

-- példa megadásra
sum1 : Bool ⊎ ℕ
sum1 = inj₁ true   -- Bool-t tartalmaz

sum2 : Bool ⊎ ℕ
sum2 = inj₂ 100    -- ℕ-t tartalmaz

-- példa használatra
f : Bool ⊎ ℕ → Bool
f = λ x → case x
            (λ b → b)
            (λ _ → true)

-- Haskell-ben:
-- f : Either Bool Nat -> Bool
-- f = \x -> case x of
--            Left b  -> b
--            Right _ -> True
