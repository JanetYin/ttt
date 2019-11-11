
-- mintaillesztés: ℕ, Bool, ⊎, ×, egyenlőség

open import lib

-- definiáld a következő függvényeket mintaillesztéssel:
--------------------------------------------------------------------------------


-- λ, proj₁, proj₂, case, _,_, inj₁, inj₂

xor : Bool → Bool → Bool
xor true false = true
xor false true = true
xor _     _    = false  -- _ mindenre illeszkedő minta

-- parancs: változót írunk lyukba,
-- C-c-C-c, akkor mintát illeszt
-- a változóra

Bool-eq : Bool → Bool → Bool
Bool-eq true true = true
Bool-eq false false = true
Bool-eq _ _ = false

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
a + zero  = a
a + suc b = suc (a + b)  -- rekurzió!

-- 2 megszorítás:
--    nincs végtelen loop
--    nincs nem teljes mintaillesztés

-- loop : ℕ → ℕ
-- loop n = loop (n + 1)

-- incomplete : Bool → Bool
-- incomplete true = true

-- p : ⊥
-- p = p

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * b = zero
suc a * b = a * b + b

ℕ-eq : ℕ → ℕ → Bool
ℕ-eq zero zero = true
ℕ-eq zero (suc y) = false
ℕ-eq (suc x) zero = false
ℕ-eq (suc x) (suc y) = ℕ-eq x y

lessThan : ℕ → ℕ → Bool
lessThan zero zero = false
lessThan zero (suc m) = true
lessThan (suc n) zero = false
lessThan (suc n) (suc m) = lessThan n m

-- extra A típusparaméter
primrec' : (A : Set) → A → (ℕ → A → A) → ℕ → A
primrec' A z s zero = z
primrec' A z s (suc n) = s n (primrec' A z s n)

-- extra A típusparaméter
ifthenelse' : (A : Set) → Bool → A → A → A
ifthenelse' A true t f = t
ifthenelse' A false t f = f

case' : (A B C : Set) → A ⊎ B → (A → C) → (B → C) → C
case' A B C (inj₁ a) f g = f a
case' A B C (inj₂ b) f g = g b

-- ℕ-egyenlőségreláció
ℕEq : ℕ → ℕ → Set
ℕEq zero   zero     = ⊤
ℕEq zero   (suc m)  = ⊥
ℕEq (suc n) zero    = ⊥
ℕEq (suc n) (suc m) = ℕEq n m

-- reflexív, tranzitív, szimm
-- ⊤ \top, ⊥ \bot

ℕEq-refl : (n : ℕ) → ℕEq n n
ℕEq-refl zero    = tt
ℕEq-refl (suc n) = ℕEq-refl n

ℕEq-sym : (n m : ℕ) → ℕEq n m → ℕEq m n
ℕEq-sym zero zero eq = tt
ℕEq-sym (suc n) (suc m) eq = ℕEq-sym n m eq

-- C-u-C-u parancs prefix: jelenítsünk meg valamit
--         kiértékelve
-- C-u     parancs prefix: jelenítsünk meg valamit
--          legkevésbé kiértékelve

ℕEq-trans : (n m k : ℕ) → ℕEq n m → ℕEq m k → ℕEq n k
ℕEq-trans zero zero zero eq1 eq2 = tt
ℕEq-trans (suc n) (suc m) (suc k) eq1 eq2 =
  ℕEq-trans n m k eq1 eq2

-- ha két szám egyenlő, akkor mindig ki lehet cserélni
-- az egyiket a másikra (pl egy adott típusban)

-- "substitution"
ℕEq-subst : (P : ℕ → Set)(n m : ℕ) → ℕEq n m → P n → P m
ℕEq-subst P zero zero eq pn = pn
ℕEq-subst P (suc n) (suc m) eq pn =
  ℕEq-subst (λ x → P (suc x)) n m eq pn

ℕEq-sym' : (n m : ℕ) → ℕEq n m → ℕEq m n
ℕEq-sym' n m eq = ℕEq-subst (λ m → ℕEq m n) n m eq (ℕEq-refl n)
