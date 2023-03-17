open import lib hiding (_+_; _*_; _-_; _<_)


xor : Bool × Bool → Bool
xor (false , false) = false
xor (false , true) = true
xor (true , false) = true
xor (true , true) = false

test-xor-1 : xor (true  , true ) ≡ false
test-xor-1 = refl
test-xor-2 : xor (true  , false) ≡ true
test-xor-2 = refl
test-xor-3 : xor (false , true ) ≡ true
test-xor-3 = refl
test-xor-4 : xor (false , false) ≡ false
test-xor-4 = refl

---------------------------------------------------------
-- random isomorphisms
------------------------------------------------------

-- case függvény
-- case : {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
-- case (inl a) ac _ = ac a
-- case (inr b) _ bc = bc b

iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
iso1 = (λ x → case (x true) (λ x₁ → inl (λ b → x₁)) λ x₁ → inr (inr (λ b → x₁))) ,
--  λ { (inl x) x₁ → {!!} ; (inr x) x₁ → {!!}} -- Ctrl-C Ctrl-r
  λ { (inl x) x₁ → inl (x x₁) ;
  (inr (inl (fst₁ , fst₂ , snd₁))) x₁ → inl fst₂ ;
  (inr (inr x)) x₁ → inr (x x₁)}

iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
iso2 = (λ x → (λ a → x (inl a)) , λ b → x (inr b))
  , λ { x (inl x₁) → fst x x₁ ; x (inr x₁) → snd x x₁}

iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ Bool ⊎ ⊤
iso3 = {!!}
testiso3 : fst iso3 (inl tt) ≡ fst iso3 (inr (inl tt)) → ⊥
testiso3 ()
testiso3' : fst iso3 (inl tt) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3'' ()

iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ (⊤ ⊎ ⊤)
iso4 = {!!} , {!!}
testiso4 : fst iso4 (λ _ → inl tt) ≡ fst iso4 (λ _ → inr (inr tt)) → ⊥
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≡ snd iso4 (inr tt) tt → ⊥
testiso4' ()

---------------------------------------------------------
-- natural numbers
---------------------------------------------------------

-- data ℕ = zero | suc ℕ

data Maybe A : Set where
  Nothing : Maybe A
  Just    : A → Maybe A

pred : ℕ → Maybe ℕ
pred zero = Nothing
pred (suc n) = Just n

zerosuc : Maybe ℕ → ℕ
zerosuc = {!!}

pred↔zerosuc-test1 : pred (zerosuc Nothing) ≡ Nothing
pred↔zerosuc-test1 = refl
pred↔zerosuc-test2 : {n : ℕ} → pred (zerosuc (Just n)) ≡ Just n
pred↔zerosuc-test2 = refl

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

--- double (suc (suc (suc zero))) ≡ double 3
--- n = suc (suc zero)
--- suc (suc (double n)) ≡ suc (suc (double (suc (suc zero))))
--- n = suc zero
--- suc (suc (suc (suc (double (suc zero)))))
--- n = zero
--- suc (suc (suc (suc (suc (suc (zero))))))

double-test1 : double 2 ≡ 4
double-test1 = refl
double-test2 : double 0 ≡ 0
double-test2 = refl
double-test3 : double 10 ≡ 20
double-test3 = refl

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

half-test1 : half 10 ≡ 5
half-test1 = refl
half-test2 : half 11 ≡ 5
half-test2 = refl
half-test3 : half 12 ≡ 6
half-test3 = refl

_+_ : ℕ → ℕ → ℕ
zero + zero = zero
zero + suc x₁ = suc x₁
suc x + zero = suc x
suc x + suc x₁ = suc (suc (x + x₁))
infixl 6 _+_

+-test1 : 3 + 5 ≡ 8
+-test1 = refl
+-test2 : 0 + 5 ≡ 5
+-test2 = refl
+-test3 : 5 + 0 ≡ 5
+-test3 = refl

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = x * y + y
infixl 7 _*_

*-test1 : 3 * 4 ≡ 12
*-test1 = refl
*-test2 : 3 * 1 ≡ 3
*-test2 = refl
*-test3 : 3 * 0 ≡ 0
*-test3 = refl
*-test4 : 0 * 10 ≡ 0
*-test4 = refl

_^_ : ℕ → ℕ → ℕ
x ^ zero = suc zero
x ^ suc x₁ = x * (x ^ x₁)
infixr 8 _^_

^-test1 : 3 ^ 4 ≡ 81
^-test1 = refl
^-test2 : 3 ^ 0 ≡ 1
^-test2 = refl
^-test3 : 0 ^ 3 ≡ 0
^-test3 = refl
^-test4 : 1 ^ 3 ≡ 1
^-test4 = refl
^-test5 : 0 ^ 0 ≡ 1
^-test5 = refl

_! : ℕ → ℕ
zero ! = suc zero
suc x ! = suc x * x !


!-test1 : 3 ! ≡ 6
!-test1 = refl
!-test2 : 1 ! ≡ 1
!-test2 = refl
!-test3 : 6 ! ≡ 720
!-test3 = refl

_-_ : ℕ → ℕ → ℕ
zero - zero = zero
zero - suc x₁ = zero
suc x - zero = suc x
suc x - suc x₁ = x - x₁
infixl 6 _-_

-test1 : 3 - 2 ≡ 1
-test1 = refl
-test2 : 3 - 3 ≡ 0
-test2 = refl
-test3 : 3 - 4 ≡ 0
-test3 = refl

_≥_ : ℕ → ℕ → Bool
zero ≥ zero = true
zero ≥ suc x₁ = false
suc x ≥ zero = true
suc x ≥ suc x₁ = x ≥ x₁

≥test1 : 3 ≥ 2 ≡ true
≥test1 = refl
≥test2 : 3 ≥ 3 ≡ true
≥test2 = refl
≥test3 : 3 ≥ 4 ≡ false
≥test3 = refl

_&&_ : Bool → Bool → Bool
true && true = true
_ && _ = false


not'' : Bool → Bool
not'' true = false
not'' false = true

-- ne hasznalj rekurziot, hanem hasznald _≥_-t!
_>_ : ℕ → ℕ → Bool
a > b = (a ≥ b) && not'' (b ≥ a)

>test1 : 3 > 2 ≡ true
>test1 = refl
>test2 : 3 > 3 ≡ false
>test2 = refl
>test3 : 3 > 4 ≡ false
>test3 = refl

not' : Bool → Bool
not' true = false
not' false = true

_<_ : ℕ → ℕ → Bool
_<_ = {!!}

<test1 : 3 < 2 ≡ false
<test1 = refl
<test2 : 3 < 3 ≡ false
<test2 = refl
<test3 : 3 < 4 ≡ true
<test3 = refl

min : ℕ → ℕ → ℕ
min = {!!}

min-test1 : min 3 2 ≡ 2
min-test1 = refl
min-test2 : min 2 3 ≡ 2
min-test2 = refl
min-test3 : min 3 3 ≡ 3
min-test3 = refl

comp : {A : Set} → ℕ → ℕ → A → A → A → A
comp m n m<n m=n m>n with m ≥ n
... | false = {!!}
... | true = {!!}

comp-test1 : comp 10 10 0 1 2 ≡ 1
comp-test1 = refl
comp-test2 : comp 10 11 0 1 2 ≡ 0
comp-test2 = refl
comp-test3 : comp 12 11 0 1 2 ≡ 2
comp-test3 = refl

-- hasznald comp-ot!
gcd : ℕ → ℕ → ℕ
{-# TERMINATING #-}
gcd m n = {!!}

gcd-test1 : gcd 6 9 ≡ 3
gcd-test1 = refl
gcd-test2 : gcd 100 150 ≡ 50
gcd-test2 = refl
gcd-test3 : gcd 17 19 ≡ 1
gcd-test3 = refl
gcd-test4 : gcd 12 24 ≡ 12
gcd-test4 = refl
gcd-test5 : gcd 19 17 ≡ 1
gcd-test5 = refl

-- hasznald ugyanazt a definiciot, mint gcd-nel, de most fuel szerinti rekurzio
gcd-helper : ℕ → ℕ → ℕ → ℕ
gcd-helper zero m n = 42
gcd-helper (suc fuel) m n = {!!}
gcd' : ℕ → ℕ → ℕ
gcd' m n = gcd-helper (m + n) m n

gcd'-test1 : gcd' 6 9 ≡ 3
gcd'-test1 = refl
gcd'-test2 : gcd' 100 150 ≡ 50
gcd'-test2 = refl
gcd'-test3 : gcd' 17 19 ≡ 1
gcd'-test3 = refl
gcd'-test4 : gcd' 12 24 ≡ 12
gcd'-test4 = refl
gcd'-test5 : gcd' 19 17 ≡ 1
gcd'-test5 = refl

not : Bool → Bool
not true = false
not false = true

even? : ℕ → Bool
even? = {!!}

even?-test1 : even? 3 ≡ false
even?-test1 = refl
even?-test2 : even? 200 ≡ true
even?-test2 = refl

fib : ℕ → ℕ
fib = {!!}

fib-test1 : fib 6 ≡ 13
fib-test1 = refl
fib-test2 : fib 3 ≡ 3
fib-test2 = refl

eq? : ℕ → ℕ → Bool
eq? = {!!}

eq?-test1 : eq? 4 3 ≡ false
eq?-test1 = refl
eq?-test2 : eq? 4 4 ≡ true
eq?-test2 = refl

-- rem m n = a maradek, ha elosztjuk m-et (suc n)-el
rem : ℕ → ℕ → ℕ
rem a b = {!!}
rem-test1 : rem 5 1 ≡ 1
rem-test1 = refl
rem-test2 : rem 11 2 ≡ 2
rem-test2 = refl

-- div m n = m-ben hanyszor van meg (suc n)
div : ℕ → ℕ → ℕ
div a b = {!!}
div-test1 : div 5 1 ≡ 2
div-test1 = refl
div-test2 : div 11 2 ≡ 3
div-test2 = refl

iteNat : {A : Set} → A → (A → A) → ℕ → A
iteNat z s zero = z
iteNat z s (suc n) = s (iteNat z s n)

recNat : {A : Set} → A → (ℕ → A → A) → ℕ → A
recNat z s zero = z
recNat z s (suc n) = s n (recNat z s n)

-- FEL: add meg iteNat-ot mintaillesztes nelkul, recNat segitsegevel
iteNat' : {A : Set} → A → (A → A) → ℕ → A
iteNat' = {!!}

iteNat'-test1 : {A : Set}{z : A}{s : A → A} → iteNat' z s zero ≡ z
iteNat'-test1 = refl
iteNat'-test2 : {A : Set}{z : A}{s : A → A}{n : ℕ} → iteNat' z s (suc n) ≡ s (iteNat' z s n)
iteNat'-test2 = refl

-- FEL: add meg recNat-ot mintaillesztes nelkul, iteNat segitsegevel (lasd eloadas)
recNat' : {A : Set} → A → (ℕ → A → A) → ℕ → A
recNat' = {!!}

recNat'-test1 : {A : Set}{z : A}{s : ℕ → A → A} → recNat' z s zero ≡ z
recNat'-test1 = refl
recNat'-test2 : {A : Set}{z : A}{s : ℕ → A → A} → recNat' z s 3 ≡ s 2 (s 1 (s 0 z))
recNat'-test2 = refl

-- FEL: add meg ujra az osszes fenti fuggvenyt mintaillesztes nelkul, iteNat es/vagy recNat hasznalataval!
