module bonus where
open import lib

-- Emacs key bindings (C = Ctrl, M = Alt):
-- C-x C-f : create or open a file
-- C-x C-s : save a file
-- C-x C-c : close Emacs
-- M-w : Copy
-- C-y : Paste
--
-- Agda-mode key bindings:
-- C-c C-l : Typecheck
-- C-c C-n : Evaluate
-- C-c C-, : Check the type of a hole
-- C-c C-. : Check the type of a hole, and the type of the expresion in the hole
-- C-c C-SPACE : Fill a hole
-- C-c C-r : Try to automatically fill a hole
-- C-c C-c : Case split.
-- C-c C-a : Try to fill a hole automatically
--
-- Symbols: λ = \lambda
--          × = \times
--          → = \r
--          ₁ = \_1
--          ₂ = \_2
--          ⊎ = \u+
--          ≤ = \le
--          ↔ = \<->
--          ⊤ = \top
--          ⊥ = \bot
--          ¬ = \neg
--          ≡ = \==
--          ∎ = \qed

infixl 4 _+_ -- x + y + z = (x + y) + z
infixl 5 _*_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc n + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + (n * m)

Eqn : ℕ → ℕ → Set
Eqn zero    zero = ⊤
Eqn zero    (suc y) = ⊥
Eqn (suc x) zero = ⊥
Eqn (suc x) (suc y) = Eqn x y

---

Eqn-transp : (P : ℕ → Set) (x y : ℕ) (p : Eqn x y) → P x → P y
Eqn-transp P zero zero p a = a
Eqn-transp P zero (suc y) p a = exfalso p
Eqn-transp P (suc x) zero p a = exfalso p
Eqn-transp P (suc x) (suc y) p a = Eqn-transp (λ z → P (suc z)) x y p a

Eqn-refl : (n : ℕ) → Eqn n n
Eqn-refl zero = tt
Eqn-refl (suc n) = Eqn-refl n

plusRightId : (x : ℕ) → Eqn (x + zero) x
plusRightId zero = tt
plusRightId (suc x) = plusRightId x

plusLeftId : (x : ℕ) → Eqn (zero + x) x
plusLeftId x = Eqn-refl x

Eqn-sym : (a b : ℕ) → Eqn a b → Eqn b a
Eqn-sym a b x = Eqn-transp (λ y → Eqn y a) a b x (Eqn-refl a)

Eqn-trans : (a b c : ℕ) → Eqn a b → Eqn b c → Eqn a c
Eqn-trans a b c p q = Eqn-transp (λ y → Eqn a y) b c q p

Eqn-cong : (x y : ℕ) → (f : ℕ → ℕ) → Eqn x y → Eqn (f x) (f y)
Eqn-cong x y f p = Eqn-transp (λ z → Eqn (f x) (f z)) x y p (Eqn-refl (f x))

---- Proofs about _+_

+-suc : (a b : ℕ) → Eqn (a + suc b) (suc (a + b))
+-suc zero b = Eqn-refl b
+-suc (suc a) b = +-suc a b

+-assoc : (a b c : ℕ) → Eqn ((a + b) + c) (a + (b + c))
+-assoc zero b c = Eqn-refl (b + c)
+-assoc (suc a) b c = +-assoc a b c

+-comm : (a b : ℕ) → Eqn (a + b) (b + a)
+-comm a zero = plusRightId a
+-comm a (suc b) = Eqn-trans (a + suc b) (suc (a + b)) (suc (b + a)) (+-suc a b) (+-comm a b)

-----

infixl 4 _⊕_
data Tree : Set where
  Zero : Tree
  V    : ℕ → Tree
  _⊕_  : Tree → Tree → Tree

eval : Tree → ℕ
eval Zero    = zero
eval (V x)   = x
eval (a ⊕ b) = eval a + eval b

flatten' : Tree → Tree → Tree
flatten' Zero    acc = acc
flatten' (V x)   acc = V x ⊕ acc
flatten' (a ⊕ b) acc = flatten' a (flatten' b acc)

flatten'-lemma : (a b : Tree)
               → Eqn (eval a + eval b)
                     (eval (flatten' a b))
flatten'-lemma Zero b = Eqn-refl (eval b)
flatten'-lemma (V x) b = Eqn-refl (x + eval b)
flatten'-lemma (x ⊕ y) b
  = Eqn-trans (eval x + eval y + eval b)
              (eval x + (eval y + eval b))
              (eval (flatten' x (flatten' y b)))
              (+-assoc (eval x) (eval y) (eval b))
   (Eqn-trans (eval x + (eval y + eval b))
              (eval x + eval (flatten' y b))
              (eval (flatten' x (flatten' y b)))
              (Eqn-cong (eval y + eval b)
                        (eval (flatten' y b))
                        (λ z → eval x + z)
                        (flatten'-lemma y b))
              (flatten'-lemma x (flatten' y b)))

flatten : Tree → Tree
flatten a = flatten' a Zero

flatten-lemma : (t : Tree) → Eqn (eval t) (eval (flatten t))
flatten-lemma t =
  let q = flatten'-lemma t Zero
  in Eqn-trans (eval t)
     (eval t + zero)
     (eval (flatten' t Zero))
     (Eqn-sym (eval t + zero) (eval t) (plusRightId (eval t)))
     q

test : (a b : ℕ) → Eqn ((a + a) + (b + b) + zero)
                       ((a + a + zero) + (b + b + zero))
test a b = let t₁ = ((V a ⊕ V a) ⊕ (V b ⊕ V b) ⊕ Zero)
               t₂ = ((V a ⊕ V a ⊕ Zero) ⊕ (V b ⊕ V b ⊕ Zero))
               ft₁ = flatten t₁
               ft₂ = flatten t₂
               p : Eqn (eval t₁) (eval ft₁)
               p = flatten-lemma t₁
               q : Eqn (eval t₂) (eval ft₂)
               q = flatten-lemma t₂
           in Eqn-trans (eval t₁) (eval ft₁) (eval t₂)
                        p (Eqn-sym (eval t₂) (eval ft₂) q)
