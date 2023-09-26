module sol-hf2 where
open import Lib

--- 1. Hozdd létre a TriBool típust, ami három top (⊤) összegtípusa
TriBool : Set
TriBool = ⊤ ⊎ ⊤ ⊎ ⊤ --- ide írd a típust!

--- 2. Mutassuk meg, hogy a TriBool kölcsönösen átjárható a Bool ⊎ ⊤ típussal

izo : TriBool ↔ Bool ⊎ ⊤
fst izo (inl a) = inl false
fst izo (inr (inl a)) = inl true
fst izo (inr (inr b)) = inr b
snd izo (inl false) = inl tt
snd izo (inl true) = inr (inl tt)
snd izo (inr b) = inr (inr b)


--- 3. Mutassuk meg, hogy a ⊤ → Bool típus kölcsönösen átjárható a Bool × ⊤ típussal

izo' : (⊤ → Bool) ↔ Bool × ⊤
fst izo' x = x tt , tt
snd izo' x _ = fst x

--- 3. Mutassuk meg, hogy a ⊥ ⊎ TriBool típus kölcsönösen átjárható a (⊤ x ⊤) ⊎ (⊤ x ⊤) ⊎ (⊤ x ⊤) típussal
izo'' : ⊥ ⊎ TriBool ↔ (⊤ × ⊤) ⊎ (⊤ × ⊤) ⊎ (⊤ × ⊤)
fst izo'' (inr (inl a)) = inl (a , a)
fst izo'' (inr (inr (inl a))) = inr (inl (a , a))
fst izo'' (inr (inr (inr b))) = inr (inr (b , b))
snd izo'' (inl a) = inr (inl (fst a))
snd izo'' (inr (inl a)) = inr (inr (inl (fst a)))
snd izo'' (inr (inr b)) = inr (inr (inr (fst b)))


--- TESZTEK NE ÍRD ÁT
test0 : (fst izo) (inl tt) ≡ inl false
test0 = refl
test1 : (fst izo) (inr (inl tt)) ≡ inl true
test1 = refl
test2 : (snd izo) (inr tt) ≡ inr (inr tt)
test2 = refl
test3 : (snd izo') (true , tt) ≡ λ _ → true
test3 = refl
test4 : (snd izo'') (inl _) ≡ inr (inl _)
test4 = refl
test5 : (snd izo'') (inr (inl _)) ≡ inr (inr (inl _))
test5 = refl
test6 : (snd izo'') (inr (inr _)) ≡ inr (inr (inr _))
test6 = refl