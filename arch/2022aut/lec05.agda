open import lib hiding (_+_; _*_)

-- λ x → (λ y → y)
-- const (λ y → y)
t t' : ℕ → ℕ
t' zero = suc zero
t' (suc n) = suc (suc (t' n))
t n = t' (suc n)

-- zerosuc, inverse of pred

half : ℕ → ℕ
half zero = 0
half (suc zero) = 0
half (suc (suc n)) = suc (half (suc n))

_+_ _*_ _^_ _^^_ : ℕ → ℕ → ℕ
a + zero  = a
a + suc b = suc (a + b)
a * zero  = 0
a * suc b = a + (a * b)    --  a + (a * b)
a ^ zero  = 1
a ^ suc b = a * (a ^ b)    -- _*_ a (_^_ a b)
a ^^ zero  = a
a ^^ suc b = a ^ (a ^^ b)

ack : ℕ → ℕ → ℕ → ℕ
ack 0 a b = suc b
ack _ a 0 = a
ack (suc m) a (suc b) = ack m a (ack (suc m) a b)

fast : ℕ → ℕ
fast n = ack n n n

-- Ackermann
-- _-_, comp, gcd

module _ {A : Type}(a<b a=b a>b : A) where
  comp : ℕ → ℕ → A
  comp zero    zero    = a=b
  comp zero    (suc b) = a<b
  comp (suc a) zero    = a>b
  comp (suc a) (suc b) = comp a b

{-
gcd0 : ℕ → ℕ → ℕ
gcd0 a b = comp (gcd0 a (b - a)) a (gcd0 (a - b) b) a b
-}

gcd1 : ℕ → ℕ → ℕ → ℕ
gcd1 zero a b = 42
gcd1 (suc fuel) a b = comp (gcd1 fuel a (b - a)) a (gcd1 fuel (a - b) b) a b

gcd : ℕ → ℕ → ℕ
gcd a b = gcd1 (a + b) a b

-- primitiv rekurzio

-- itBool : {A : Type} → A → A → Bool → A
itℕ : {A : Type} → A → (A → A) → ℕ → A
-- fold, catamorphism, nondependent eliminator, destructor, recursor
itℕ z s zero = z
itℕ z s (suc n) = s (itℕ z s n)

-- challenge: itℕ-el megadni a pred-et

recℕ : {A : Type} → A → (ℕ → A → A) → ℕ → A
recℕ z s zero = z
recℕ z s (suc n) = s n (recℕ z s n)

pred : ℕ → ℕ ⊎ ⊤
pred n = recℕ (inr tt) (λ n _ → inl n) n

-- challenge: recℕ-t megadni itℕ-el

_*2+3 : ℕ → ℕ
_*2+3 = itℕ 3 (λ n → suc (suc n))

_+'_ : ℕ → ℕ → ℕ
a +' b = itℕ b suc a

-- lists, trees

data List (A : Type) : Type where
  []  : List A                                         -- nil
  _∷_ : A → List A → List A -- Haskell : ::   Agda     -- cons
                            -- lengyel s sz   magyar
-- data List A = [] | A ∷ List A      (GADT jeloles)

map : {A B : Type} → (A → B) → List A → List B
map f [] = []
map f (a ∷ ak) = f a ∷ map f ak

head : {A : Type} → List A → A ⊎ ⊤
head [] = inr tt
head (a ∷ _) = inl a

itList : {A B : Type} → B → (A → B → B) → List A → B
itList n c [] = n
itList n c (a ∷ ak) = c a (itList n c ak)

-- remove zero from ℕ, show that it is empty

data Tree : Type where
  leaf : Tree
  node : Tree → Tree → Tree

data Nat' : Type where
  suc : Nat' → Nat'

f : Nat' → ⊥
f (suc n) = f n

{-# NO_POSITIVITY_CHECK #-}
data Weird : Type where
  weird : (Weird → ⊥) → Weird

data Notweird : Type where
   notweird : (ℕ → Notweird) → Notweird

hf : ⊥
hf = {!!} -- hasznald Weird-et!

-- noWeird : Weird → ⊥
-- problem : ⊥

-- inductive types are built iteratively

-- coproduct = sum, counit
-- stream, _∷_, from : ℕ → Stream ℕ, ezt listakra nem lehet, filter



-- MAJD: szorzat tipust data-val
-- MAJD: nezzuk meg a tipusosztalyok implementaciojat Agdaban

-- kovetkezo ora egy perccel rovidebb

