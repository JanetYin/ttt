    module libN where
open import lib

pred' : ℕ → ℕ ⊎ ⊤
pred' = indℕ (λ _ → ℕ ⊎ ⊤) (inj₂ tt) (λ n _ → inj₁ n)

eq0 : ℕ → Bool
eq0 = rec true (λ _ → false)

eqℕ : ℕ → ℕ → Bool
eqℕ = rec eq0 (λ eqn m → case (pred' m) eqn (λ _ → false))

-- what is the difference between eqℕ a b and Eqℕ a b?
Eqℕ : ℕ → ℕ → Set
Eqℕ = λ a b → if eqℕ a b then ⊤ else ⊥

-- reflexivity
reflℕ : (a : ℕ) → Eqℕ a a
reflℕ = indℕ (λ x → Eqℕ x x) tt λ _ e → e

-- transport
transpℕ : (a b : ℕ) → Eqℕ a b → (P : ℕ → Set) → P a → P b
transpℕ = indℕ (λ a → (b : ℕ) → Eqℕ a b → (P : ℕ → Set) → P a → P b)
                (indℕ (λ b → Eqℕ zero b → (P : ℕ → Set) → P zero → P b)
                      (λ _ _ P0 → P0)
                      λ _ _ b _ _ → exfalso b  )
                λ n ih → indℕ (λ b → Eqℕ (suc n) b → (P : ℕ → Set) → P (suc n) → P b)
                               (λ b _ _ → exfalso b)
                               λ n ihb e P Psucn → ih n e (λ x → P (suc x)) Psucn 

-- commutativity of equality of ℕ: use transpℕ!
sym : (a b : ℕ) → Eqℕ a b → Eqℕ b a
sym a b e = transpℕ a b e (λ x → Eqℕ x a) (reflℕ a)

-- transitivity of equality of ℕ: use transpℕ!
trans : (a b c : ℕ) → Eqℕ a b → Eqℕ b c → Eqℕ a c
trans a b c e e' = transpℕ b c e' (λ x → Eqℕ a x) e

-- congruence: use transpℕ!
cong : (f : ℕ → ℕ) → (a b : ℕ) → Eqℕ a b → Eqℕ (f a) (f b)
cong f a b e = transpℕ a b e (λ b → Eqℕ (f a) (f b)) (reflℕ (f a))

-- disjointness of different constructors of ℕ
disj : (a : ℕ) → ¬ Eqℕ zero (suc a)
disj =  λ _ e → e

-- injectivity of suc
inj : (a b : ℕ) → Eqℕ a b → Eqℕ (suc a) (suc b)
inj = λ a b e → e

-- addition
_+_ : ℕ → ℕ → ℕ
_+_ = λ a b → rec b suc a
infixl 5 _+_

-- properties of addition

-- no need for indℕ
idl : (a : ℕ) → Eqℕ (0 + a) a
idl = reflℕ

-- use indℕ
idr : (a : ℕ) → Eqℕ (a + 0) a
idr = indℕ (λ a → Eqℕ (a + 0) a) (reflℕ 0) (λ _ e → e)

-- use indℕ
ass : (a b c : ℕ) → Eqℕ ((a + b) + c) (a + (b + c))
ass = λ a b c → indℕ
  (λ a → Eqℕ ((a + b) + c) (a + (b + c)))
  (reflℕ (b + c))
  (λ _ e → e)
  a

-- use indℕ
suc+ : (a b : ℕ) → Eqℕ (suc a + b) (a + suc b)
suc+ = λ a b → indℕ
  (λ a → Eqℕ (suc a + b) (a + suc b))
  (reflℕ (1 + b))
  (λ _ e → e)
  a

-- use indℕ, trans, suc+
comm : (a b : ℕ) → Eqℕ (a + b) (b + a)
comm = λ a b → indℕ
  (λ a → Eqℕ (a + b) (b + a))
  (sym (b + 0) b (idr b))
  (λ n e → trans (suc n + b) (suc b + n) (b + suc n) e (suc+ b n))
  a

_*_ : ℕ → ℕ → ℕ
_*_ = λ a b → rec 0 (_+_ b) a
infixl 7 _*_

-- laws for muliplication

-- use indℕ
idl* : (a : ℕ) → Eqℕ (1 * a) a
idl* = indℕ (λ a → Eqℕ (1 * a) a) (reflℕ 0) (λ _ e → e)

-- use indℕ
idr* : (a : ℕ) → Eqℕ (a * 1) a
idr* = indℕ (λ a → Eqℕ (a * 1) a) (reflℕ 0) (λ _ e → e)

-- no need for indℕ
nulll : (a : ℕ) → Eqℕ (0 * a) 0
nulll =  λ _ → reflℕ 0

-- use indℕ
nullr : (a : ℕ) → Eqℕ (a * 0) 0
nullr = indℕ (λ a → Eqℕ (a * 0) 0) (reflℕ 0) (λ _ e → e)

-- trans egy kényelmesebb változata \sq5
_◾_ : {a b c : ℕ} → Eqℕ a b → Eqℕ b c → Eqℕ a c
_◾_ {a}{b}{c} = trans a b c


{-
Biz be teljes indukcioval:
a = 0 esetre
  (0 + b) * c = 0 * c + b * c    (idl+/def)
  b * c       = 0 * c + b * c    (nulll/def)
  b * c       = 0 + b * c        (idl+/def)
  b * c       = b * c
a = n + 1 esetre tfh h ih: (n + b) * c = n * c + b * c
((n + 1) + b) * c = (n + 1) * c + b * c  
((n + 1) + b) * c   =            (def)
(1 + (n + b)) * c   =            (def)
c + (n + b) * c     =            (cong, ih)
c + (n * c + b * c) =            (ass)
(c + n * c) + b * c =            (def)
(n + 1) * c + b * c 
-}

-- use indℕ, trans, cong, sym, ass
distr : (a b c : ℕ) → Eqℕ ((a + b) * c) (a * c + b * c)
distr = λ a b c → indℕ
  (λ a → Eqℕ ((a + b) * c) (a * c + b * c))
  (reflℕ (b * c))
  (λ n e → trans
    ((suc n + b) * c)
    (c + (n * c + b * c))
    (suc n * c + b * c)
    (cong (_+_ c) ((n + b) * c) (n * c + b * c) e)
    (sym (suc n * c + b * c) (c + (n * c + b * c)) (ass c (n * c) (b * c))))
  a

-- use indℕ, trans, distr, cong
ass* : (a b c : ℕ) → Eqℕ ((a * b) * c) (a * (b * c))
ass* = λ a b c → indℕ
  (λ a → Eqℕ ((a * b) * c) (a * (b * c)))
  tt
  (λ n e → trans
    (suc n * b * c)
    (b * c + (n * b) * c)
    (suc n * (b * c))
    (distr b (n * b) c)
    (cong (_+_ (b * c)) ((n * b) * c) (n * (b * c)) e))
  a

-- use indℕ, trans, sym, ass, cong, comm
suc* : (a b : ℕ) → Eqℕ (a + a * b) (a * suc b)
suc* = λ a b → indℕ
  (λ a → Eqℕ (a + a * b) (a * suc b))
  (reflℕ 0)
  (λ n e → trans
    (suc n + suc n * b)
    (suc b + (n + n * b))
    (suc n * suc b)
    (trans
      (n + (b + n * b))
      ((n + b) + n * b)
      (b + (n + n * b))
      (sym (n + b + n * b) (n + (b + n * b)) (ass n b (n * b)))
      (trans
        ((n + b) + n * b)
        ((b + n) + n * b)
        (b + (n + n * b))
        (cong (_+ (n * b)) (n + b) (b + n) (comm n b))
        (ass b n (n * b))))
    (cong (_+_ (suc b)) (n + n * b) (n * suc b) e))
  a

-- use indℕ, nullr, trans, suc*
comm* : (a b : ℕ) → Eqℕ (a * b) (b * a)
comm* = λ a b → indℕ
  (λ a → Eqℕ (a * b) (b * a))
  (sym (b * zero) zero (nullr b))
  (λ n e → trans
    (suc n * b)
    (b + b * n)
    (b * suc n)
    (cong (_+_ b) (n * b) (b * n) e)
    (suc* b n))
  a

{-
a * (b + c) = (comm)
(b + c) * a = (distr)
b * a + c * a = (comm)
a * b + c * a = (comm)
a * b + a * c
-}

-- left distributivity: use comm* and distr
distl : (a b c : ℕ) → Eqℕ (a * (b + c)) (a * b + a * c)
distl = λ a b c → trans
  (a * (b + c))
  ((b + c) * a)
  (a * b + a * c)
  (comm* a (b + c))
  (trans
    ((b + c) * a)
    (b * a + c * a)
    (a * b + a * c)
    (distr b c a)
    (trans
      (b * a + c * a)
      (a * b + c * a)
      (a * b + a * c)
      (cong (λ x → x + c * a) (b * a) (a * b) (comm* b a))
      (cong (λ x → a * b + x) (c * a) (a * c) (comm* c a))))
