open import Agda.Builtin.Equality
open import Lib.Bool
open import Lib.Sum
open import Lib.Sigma

-- Írj izomorfizmust az A ⊎ A és a Bool × A típusok között;
-- úgy, hogy bármilyen A típussal működjön.

{-
tfh. A = ⊤
inl tt; inr tt
true , tt; false , tt

tfh. A = {a1, a2, a3} -- ez nem agdás jelölés
inl a1; inl a2; inl a3; inr a1; inr a2; inr a3
true , a1; true , a2; true , a3; false , a1; false , a2; false , a3
-}

iso : {A : Set} -> A ⊎ A ↔ Bool × A
fst iso ava = case ava (λ a -> true , a) (λ a -> false , a)
-- snd iso (b , a) = if b then (inl a) else (inr a)
snd iso (false , a) = inr a
snd iso (true , a) = inl a

testiso1 : {A : Set} -> ∀ (ava : A ⊎ A) -> snd iso (fst iso ava) ≡ ava
testiso1 (inl a) = refl
testiso1 (inr b) = refl
testiso2 : {A : Set} -> ∀ (ba : Bool × A) -> fst iso (snd iso ba) ≡ ba
testiso2 (false , a) = refl
testiso2 (true ,  a) = refl
