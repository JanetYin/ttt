open import lib

---------------------------------------------------------
-- equality
------------------------------------------------------

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl Px = Px

---------------------------------------------------------
-- properties of +,*
------------------------------------------------------

idl+ : (n : ℕ) → zero + n ≡ n
idl+ n = refl

idr+ : (n : ℕ) → n + zero ≡ n
idr+ zero = refl
idr+ (suc n) = cong suc (idr+ n)    -- arra rájön, hogy suc n + zero ≡ suc (n + zero)

ass+ : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass+ zero n o = refl
ass+ (suc m) n o = {!!}
{-
suc m + n + o = suc (m + n) + o = suc (m + n + o) -- erre ő rájön

innentől cong suc és indukciós feltevés
-}

comm+-helper : (n m : ℕ) → suc n + m ≡ n + suc m
comm+-helper zero m = refl
comm+-helper (suc n) m = cong suc (comm+-helper n m)

comm+ : (m n : ℕ) → m + n ≡ n + m
comm+ zero n = sym (idr+ n)
comm+ (suc m) n = trans (cong suc (comm+ m n)) (comm+-helper n m)
{-
ő rájön
comm+
aztán ő rájön
comm+-helper
suc m + n = suc (m + n) = suc (n + m) = suc n + m = n + suc m
-}

{-
miért jó így?
maga is rájön, hogy
(suc n + o) * m = (suc (n + o)) * m = m + (n + o) * m
-}
dist+* : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m            -- \equiv
dist+* m zero o = refl
dist+* m (suc n) o = trans (cong (m +_) (dist+* m n o))
                           (sym (ass+ m (n * m) (o * m)))
{-
               dist+*               ass+
m + (n + o) * m = m + (n * m + o * m) = m + n * m + o * m
-}

nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* = {!!}

idl* : (n : ℕ) → 1 * n ≡ n
idl* = idr+              --C-c C-z

idr* : (n : ℕ) → n * 1 ≡ n
idr* = {!!}

ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* = {!!}

comm*-helper : (n m : ℕ) → n + n * m ≡ n * suc m
comm*-helper zero m = refl
comm*-helper (suc n) m = cong suc (trans (sym (ass+ n m (n * m)))
                                  (trans (cong (_+ (n * m)) (comm+ n m))
                                  (trans (ass+ m n (n * m))
                                         (cong (m +_) (comm*-helper n m)))))
{-
               ass+             comm+             ass+       comm*-helper
n + (m + n * m) = (n + m) + n * m = m + n + n * m = m + (n + n * m) = m + n * suc m
-}

comm* : (m n : ℕ) → m * n ≡ n * m
comm* zero n = sym (nullr* n)
comm* (suc m) n = trans (cong (n +_) (comm* m n)) (comm*-helper n m)
{-
        comm*       comm*-helper
n + (m * n) = n + (n * m) = n * suc m
-}
