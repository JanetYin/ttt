open import Lib hiding (Fin)
open import Lib.Containers.Vector hiding (length; _++_)
open import Lib.Containers.List hiding (length; _++_)

f1 f2 f3 f4 f5 f6 : (b : Bool) → Lib.Fin (if b then 2 else 3)
f1 false = zero           -- 00
f1 true  = zero
f2 false = suc zero       -- 01
f2 true  = zero
f3 false = suc (suc zero) -- 02
f3 true  = zero
f4 false = zero           -- 10
f4 true  = suc zero
f5 false = suc zero       -- 11
f5 true  = suc zero
f6 false = suc (suc zero) -- 12
f6 true  = suc zero

-- ennek nincs eleme:
g : (b : Bool) → Lib.Fin (if b then 2 else 0)
g false = {!!}
g true  = {!!}

-- Fin magyarazat
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
{-
m | Fin m
-----------------------------------------------------------------------------
0 |
  |
1 | zero{0}
  |         \
2 | zero{1}   suc(zero{0})
  |         \              \
3 | zero{2}   suc(zero{1})   suc(suc(zero{0}))
  |         \              \                   \
4 | zero{3}   suc(zero{2})   suc(suc(zero{1}))   suc(suc(suc(zero{0})))
  |
  ...
-}

_+23_ : Fin 2 → Fin 3 → Fin 4
zero +23 (zero{2}) = zero
zero +23 suc zero = suc zero
zero +23 suc (suc zero) = suc (suc zero)
suc zero +23 zero = suc zero
suc zero +23 suc zero = suc (suc zero)
suc zero +23 suc (suc zero) = suc (suc (suc zero))

-- _+Fin_ : {n m : ℕ} → Fin n → Fin m → Fin (n + m)
-- _+Fin_ : {n m : ℕ} → Fin(suc n) → Fin(suc m) → Fin (suc(n + m))
-- _+Fin_ {0}{0} : Fin 1 → Fin 1 → Fin 1
-- _+Fin_ {0}{1} : Fin 1 → Fin 2 → Fin 2
-- _+Fin_ {0}{m} : Fin 1 → Fin(suc m) → Fin(suc m)

-- HF: gondolkozni, hogy ezt hogy kell megadni

-- Π (product) es Σ, specialis esetek
{-

         Π     Σ
        / \   / \
       /   \ /   \
      →     ×     ⊎

(x : ℕ) → ℕ                                      =    ℕ → ℕ
(x : ℕ) → Vec Bool x                               nincs nemfuggo valtozata
Bool → A                                         ≅    A × A
(b:Bool) → if b then A else B                    ≅    A × B
(b:Bool) → if b then Fin 7 else Fin 6            ≅ Fin 7 × Fin 6

Σ ℕ (λ _ → Bool)                                 = ℕ × Bool
Σ A (λ _ → B)                                    =: A × B
Σ Bool (λ b → if b then A else B)                ≅  A ⊎ B
Σ Bool (λ b → if b then Date else Date × Date)   ≅   Date ⊎ (Date × Date)

(n : ℕ) → Fin n = Π ℕ Fin = 0 * 1 * 2 * 3 * 4 * ... = Π_{n:ℕ} . n = 0
(n : ℕ) → Fin(suc n) = Π_{n:ℕ⁺}.n
F : ℕ → Set
F 0 = 1
F 1 = 2
F 2 = 1
F 3 = 3
F _ = 1

Π ℕ F
(n : ℕ) → F n  = F 0 * F 1 * F 2 * F 3 * ... = 1 * 2 * 1 * 3 * 1 * 1 * 1 * ...

(b : Bool) → if b then A else B = A * B

F : Fin n → Set
(i : Fin n) → F i = F 0 * F 1 * F 2 * ... * F (n-1)

F : Fin n → Set
Σ (Fin n) F = F 0 + F 1 + F 2 + ... + F (n-1)

F : Bool → Set
Σ Bool F = F false + F false

F : ℕ → Set
Σ ℕ F = F 0 + F 1 + F 2 + F 3 + ...

Fin (n + m)               ≅ Fin n ⊎ Fin m             A ⊎ B, ahol |A|=n és |B|=m, ott |A⊎B|=n+m
Fin (n * m)               ≅ Fin n × Fin m
Fin (n ^ m)               ≅ Fin m → Fin n
Fin (Π_{i:=0..n-1}(f(i))) ≅ (i:Fin n) → Fin(f i)                  f : Fin n → ℕ
Fin (Σ_{i:=0..n-1}(f(i))) ≅ Σ (Fin n) (λ i → Fin(f i))            f : Fin n → ℕ

HF: ezeket Agdaban megcsinalni
-}

-- nagyon szep HF
α : {n m : ℕ} → Fin (n ^' m) → Fin m → Fin n
α i = {!!}

α' : Fin (2 ^' 3) → Fin 3 → Fin 2
α' zero                                           = λ { zero → zero     ; (suc zero) → zero     ; (suc (suc zero)) → zero     }
α' (suc zero)                                     = λ { zero → zero     ; (suc zero) → zero     ; (suc (suc zero)) → suc zero }
α' (suc (suc zero))                               = λ { zero → zero     ; (suc zero) → suc zero ; (suc (suc zero)) → zero     }
α' (suc (suc (suc zero)))                         = λ { zero → zero     ; (suc zero) → suc zero ; (suc (suc zero)) → suc zero }
α' (suc (suc (suc (suc zero))))                   = λ { zero → suc zero ; (suc zero) → zero     ; (suc (suc zero)) → zero     }
α' (suc (suc (suc (suc (suc zero)))))             = λ { zero → suc zero ; (suc zero) → zero     ; (suc (suc zero)) → suc zero }
α' (suc (suc (suc (suc (suc (suc zero))))))       = λ { zero → suc zero ; (suc zero) → suc zero ; (suc (suc zero)) → zero     }
α' (suc (suc (suc (suc (suc (suc (suc zero))))))) = λ { zero → suc zero ; (suc zero) → suc zero ; (suc (suc zero)) → suc zero }

-- kovetkezo ora 3 perccel rovidebb: LOGIKA

