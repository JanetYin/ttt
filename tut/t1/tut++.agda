module tut.t1.tut++ where

open import lib

-- ha n < m, akkor legyen a Bool false
dec_by_ : ℕ → ℕ → (ℕ × Bool)
dec n by m = {!!}

-- ha m = 0, n mod m = 0 , false 
-- nem kell feltétlenül használni az előzőt
-- (ez a feladat nem trivi)
_mod_ : ℕ → ℕ → (ℕ × Bool)
n mod m = {!!}

-- ha a mod megvan, ez már csak a jutalom :)
isPrime : ℕ → Bool
isPrime n = {!!}
                                                
-- wikipédia szerint ez legit
e1 : ({A B : Set} → ¬ (A × B) → (¬ A ⊎ ¬ B)) →  
  {A : Set} → ¬ A ⊎ ¬ ¬ A ↔ ⊤
e1 dm = {!!}
      , {!!}

-- listákkal felvértezve, próbáljatok Eratoszthenészi szitát implementálni
