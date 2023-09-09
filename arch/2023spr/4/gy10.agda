open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Equality

---------------------------------------------------------
-- library
------------------------------------------------------

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl p = p

ass+ : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
ass+ zero    b c = refl
ass+ (suc a) b c = cong suc (ass+ a b c)

idr+ : (a : ℕ) → a + 0 ≡ a
idr+ zero    = refl
idr+ (suc a) = cong suc (idr+ a)

+suc : (a b : ℕ) → suc a + b ≡ a + suc b
+suc zero    b = refl
+suc (suc a) b = cong suc (+suc a b)

comm+ : (a b : ℕ) → a + b ≡ b + a
comm+ zero b = sym (idr+ b)
comm+ (suc a) b = trans (cong suc (comm+ a b)) (+suc b a)

dist+* : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m
dist+* m zero o = refl
dist+* m (suc n) o = trans (cong (m +_) (dist+* m n o)) (sym (ass+ m (n * m) (o * m)))

nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* zero = refl
nullr* (suc n) = nullr* n

idl* : (n : ℕ) → 1 * n ≡ n
idl* n = idr+ n

idr* : (n : ℕ) → n * 1 ≡ n
idr* zero = refl
idr* (suc n) = cong suc (idr* n)

ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* zero n o = refl
ass* (suc m) n o = trans (dist+* o n (m * n)) (cong (n * o +_) (ass* m n o))

comm*-helper : (n m : ℕ) → n + n * m ≡ n * suc m
comm*-helper zero m = refl
comm*-helper (suc n) m = trans (cong suc (trans (sym (ass+ n m (n * m))) (trans (cong (_+ n * m) (comm+ n m)) (ass+ m n (n * m))))) (cong (λ z → suc (m + z)) (comm*-helper n m))

comm* : (m n : ℕ) → m * n ≡ n * m
comm* zero n = sym (nullr* n)
comm* (suc m) n = trans (cong (n +_) (comm* m n)) (comm*-helper n m)

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 x y = trans (cong (λ t → x + t + x) (idr+ y))
        (trans (comm+ (x + y) x)
        (trans (sym (ass+ x x y))
               (cong (λ t → x + t + y) (sym (idr+ x)))))
{-
suc (suc zero) * x = x + (suc zero) * x = x + (x + zero * x) = x + (x + zero)

                 idr+         comm+         ass+        idr+
x + (y + zero) + x = (x + y) + x = x + (x + y) = x + x + y = x + (x + zero) + y
-}

-- házi
p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 = {!!}

-- házi
p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 = {!!}

-- ez nehezebb
[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 = {!!}

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)
infixr 9 _^_

-- ami ez alatt van, házi (hasonló a szorzásoshoz, csak a kitevőre kell mintát illeszteni)

p1 : (a b : ℕ) → (a + b) ^ 2 ≡ a ^ 2 + 2 * a * b + b ^ 2
p1 = {!!}

0^ : (n : ℕ) → 0 ^ (suc n) ≡ 0
0^ = {!!}

^0 : (a : ℕ) → a ^ 0 ≡ 1
^0 = {!!}

^1 : (a : ℕ) → a ^ 1 ≡ a
^1 = {!!}

^+ : (a m n : ℕ) → a ^ (m + n) ≡ a ^ m * a ^ n
^+ = {!!}

*^ : (a b n : ℕ) → (a * b) ^ n ≡ a ^ n * b ^ n
*^ = {!!}

^* : (a m n : ℕ) → a ^ (m * n) ≡ (a ^ m) ^ n
^* = {!!}

1^ : (n : ℕ) → 1 ^ n ≡ 1
1^ zero = refl
1^ (suc n) = trans (idr+ (1 ^ n)) (1^ n)

------------------------------------------------------
-- zh-feladat megoldása
------------------------------------------------------

lastOne : (a b : ℕ) → b + a + a * 1 ^ b + b * 1 ≡ 2 * (a + b)
lastOne a b = trans (cong (λ t → t + a * 1 ^ b + b * 1) (comm+ b a))
             (trans (cong (λ t → a + b + a * 1 ^ b + t) (idr* b))
             (trans (cong (λ t → a + b + a * t + b) (1^ b))
             (trans (cong (λ t → a + b + t + b) (idr* a))
             (trans (ass+ (a + b) a b)
                    (cong (λ t → a + b + t) (sym (idr+ (a + b))))))))

{-
                            comm+                       idr*
((b + a) + a * 1 ^ b) + b * 1 = a + b + a * 1 ^ b + b * 1 = a + b + a * 1 ^ b + b =
      1^                 idr*                 ass+              idr+
       = a + b + a * 1 + b = ((a + b) + a) + b = a + b + (a + b) = a + b + (a + b + zero)
-}

-- segítség: nézz fel;)
