open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

-- Próbálkozzatok az alábbi szövegek lemásolásával. Ennél a röpi könnyebb lesz; főleg abban, hogy nem lesz benne annyi idegen szimbólum. De itt is igyekszem szólni, ha valami új van; meg ott is írom majd, ha valami olyan van, amit órán nem mondtam.
-- És megnézhetitek a gyakfájlt közben, szóval nem kell fejből tudni mindent, csak annyira, hogy az időbe beleférj majd ott.

-- ² : \^2 (igazából minden felső indexes dolog így van)
-- ≡ : \equiv
-- ≢ : \nequiv
-- ⊤ : \top
-- ⊥ : \bot

-- ennek mintájára:
{-
(x - u) ² + (y - v) ² = r ²
x ² + y ² - 2 * u * x - 2 * v * y + u ² + v ² - r ² = 0
-}

-- görög:
-- Βασιλεια Ρωμαιων (Basileia Romaion)

{-
egy kis copy-paste:

ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
ezt tizenötször
-}

-- és igazi Agda-szövegek:

data ⊥ : Set where

add3' : ℕ → ℕ
add3' = λ x → x + 3

add : ℕ → ℕ → ℕ
add = {!!}

_≢0 : ℕ → Bool
zero ≢0 = false
_ ≢0 = true

--⇒ a \r2, a sima → nyílra pedig \r1-gyel tudsz visszaváltani

0<n⇒n≢0 : ∀ n -> (0 < n) ≡ true -> (n ≢0) ≡ true
0<n⇒n≢0 zero ()
0<n⇒n≢0 (suc _) 0<n = refl
