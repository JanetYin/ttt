open import Lib

     -- v ő a fuel; ha ez nullára csökken, megáll
coMax : ℕ -> ℕ∞ -> ℕ∞ -> Maybe ℕ∞
coMax zero n m = nothing
coMax (suc fuel) n m   with (pred∞ n)
coMax (suc fuel) n m | just pn  with (pred∞ m)
coMax (suc fuel) n m | just pn | just pm  with coMax fuel pn pm
coMax (suc fuel) n m | just pn | just pm | nothing = nothing
coMax (suc fuel) n m | just pn | just pm | just pres = {!!}
coMax (suc fuel) n m | just pn | nothing = just n
coMax (suc fuel) n m | nothing = just m

-- tesztek:
test1 : coMax 0 4 0 ≡ nothing
test1 = refl

test2 : coMax 1 4 0 ≡ just 4
test2 = refl

test3 : coMax 4 2 3 ≡ just 3
test3 = {!!}
