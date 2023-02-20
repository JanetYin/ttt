-- Mentes: C-x C-s
-- Buffer valtas: C-x b

-- \bN = ℕ
-- \b2 = 𝟚

module gy02.valami where

open import lib

-- Lyuk típusának lekérdezése: C-c C-,
-- Lyuk több infó: C-c C-.
-- Lyuk típus ellenőrzés és beírás: C-c C-SPC
-- Auto: C-c C-a

esik-az-eső süt-a-nap : 𝟚
esik-az-eső = tt
süt-a-nap = ff

szivarvany : 𝟚 -> 𝟚 → 𝟚
--                 esik      süt     szivarvany
--szivarvany esik süt =  if esik then (if süt then tt else ff) else ff

van-e-szivarvany : 𝟚
van-e-szivarvany = szivarvany esik-az-eső süt-a-nap

-- \r    = →
-- \-> = →
-- \to  = →
-- \Gl = λ
-- \lambda = λ
-- \lamda = λ

not : 𝟚 → 𝟚

and : 𝟚 → 𝟚 → 𝟚
and = λ a → if a then (not) else (λ x → ff)

not = λ a → if a then ff else tt

szivarvany esik süt = and esik süt


-- Kijelölés: C-SPC
-- Betöltés: C-c C-l

{-
kutyafül : Set
kutyafül = {!!}
-}

-- y : kutyafül
-- y = {!!}

--x : ∀{i}(P : lib.ℕ → Set i) → P lib.zero → ((n : lib.ℕ) → P n → P (lib.suc n)) → (t : lib.ℕ) → P t
--x = {!!}


