open import Lib hiding (_+_; _*_; _^_; Bool; true; false; if_then_else_; pred; pred')


-- (λ x → x) ≠ (λ x → if x then true else false)

-- →      (λ x → t) u = t[x↦u]          (β)
--        f = (λ x → f x)               (η)
-- ⊎      case f g (inj₁ a) = f a       (β₁)
--        case f g (inj₂ b) = g b       (β₂)
-- Bool   if true then u else v = u     (β₁)
--        if fasle then u else v = v    (β₂)
-- ×      fst (u , v) = u               (β₁)
--        snd (u , v) = v               (β₂)
--        w = (fst w , snd w)           (η)
-- ⊤      w = tt                        (η)

-- (λ x → case x (λ y → true) (λ z → true)) = (λ x → true)
{-
snd (1 , 3) =(×β₂) 3 =(×β₁) = fst (3 , 1)
case (inl (λ x → x)) (λ y → y true) (λ z → false) =(⊎β₁)
  (λ y → y true) (λ x → x) =(→β) (λ x → x) true = true ≠ false
(λ (x : ⊤ × ⊤) → (fst x , snd x)) =(⊤η) (λ x → (tt,tt)) =(⊤η) (λ x → (snd x , fst x))

(λ (x : Bool × Bool) → (fst x , snd x)) = (λ x → (snd x , fst x))
-----------------------------------------------------------------
(λ (x : Bool × Bool) → (fst x , snd x)) (true,false) = (λ x → (snd x , fst x)) (true,false)
-----------------------------------------------------------------
(true , false) = (false , true)
-------------------------------
true = false



(λ x → case x (λ y → true) (λ z → true)) = (λ x → true)

case (inl (λ x → x)) (λ y → y true) (λ z → false) =(⊎β₁)
 (λ y → y true) (λ x → x) = (→β)
 (λ x → x) true =(→β)
 true

(λ x → fst x) = (λ x → snd x)

(u v : ⊤ × ⊤)
----------------
u =(×η) (fst u , snd u) =(⊤η) (tt , tt) =(⊤η) (fst v , snd v) =(×η) v

f g : A → ⊤
--------------------------------------------------------------
f =(→η) (λ x → f x) =(⊤η) (λ x → tt) =(⊤η) (λ x → g x) =(→η) g
-}

-- x : Bool ⊢ f : A
-- ---------------------------------------(Boolη)
-- f = if x then f[x↦true] else f[x↦false]




-- (λ x → x + 0) =? (λ x → 0 + x)

Bool = ⊤ ⊎ ⊤
true false : Bool
true = inl tt
false = inr tt
if_then_else_ : {A : Set} → Bool → A → A → A
if inl _ then u else v = u
if inr _ then u else v = v
{-
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
-}
-- ℕ = {zero, suc zero, suc (suc zero), suc (suc (suc zero)), suc(suc (suc (suc zero)),), ...}

double : ℕ → ℕ
double zero = zero
double (suc x) = suc (suc (double x))
-- double (suc (suc (suc zero))) = 
-- suc (suc (double (suc (suc zero)))) = 
-- suc (suc (suc (suc (double (suc zero))))) = 
-- suc (suc (suc (suc (suc (suc (double zero)))))) = 
-- suc (suc (suc (suc (suc (suc zero)))))

_+_ : ℕ → ℕ → ℕ
m + zero  = m
m + suc n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
m * zero  = zero
m * suc n = m + (m * n)

_^_ : ℕ → ℕ → ℕ
m ^ zero  = suc zero
m ^ suc n = m * (m ^ n)

ack : ℕ → ℕ → ℕ → ℕ
ack zero                      m n       = suc n
ack (suc zero)                m zero    = m  -- +
ack (suc (suc zero))          m zero    = zero -- *
ack (suc (suc (suc zero)))    m zero    = suc zero -- ^
ack (suc (suc (suc (suc i)))) m zero    = m    -- ez lehet mas is
ack (suc l)                   m (suc n) = ack l m (ack (suc l) m n)

fast : ℕ → ℕ
fast n = ack n n n

-- ℕ iteratora

ite : {A : Set} → A → (A → A) → ℕ → A
ite z s zero    = z
ite z s (suc n) = s (ite z s n)

+-ite : ℕ → ℕ → ℕ
+-ite m n = ite m suc n

double-ite : ℕ → ℕ
double-ite n = ite zero (λ x → suc (suc x)) n

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

peldaLista : List ℕ -- [1,2,3]
peldaLista = cons 1 (cons 2 (cons 3 nil))

iteList : {A C : Set} → C → (A → C → C) → List A → C -- = foldr
iteList z s nil        = z
iteList z s (cons b n) = s b (iteList z s n)

map : {A B : Set} → (A → B) → List A → List B
map f = iteList    nil (λ a → cons (f a))

_++_ : {A : Set} → List A → List A → List A
_++_ xs = iteList xs cons

head : {A : Set} → List A → Maybe A
head nil = nothing
head (cons x xs) = just x

pred' : ℕ → ℕ
pred' zero    = zero
pred' (suc n) = n

-- HF: probaljatok megadni ite-vel!

-- "Maybe A = A ⊎ ⊤"
-- data Maybe (A : Set) : Set
--   nothing : Maybe A
--   just    : A → Maybe A

pred : ℕ → Maybe ℕ
pred zero    = nothing
pred (suc n) = just n

zerosuc : Maybe ℕ → ℕ
zerosuc (just n) = suc n
zerosuc nothing = zero

-- HF: pred (zerosuc u) = u
--     zerosuc (pred u) = u

-- λ x → pred (zerosuc x) ≠ λ x → x

-- termeszetes szamokra meg elmeletileg sem tudunk η szabalyt csinalni

-- data-val megadott tipusokra nincs η, hanem pattern match van es kesz
-- induktiv tipusok

-- kov. ora 2 perccel rovidebb


