module gy10 where

open import Lib

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------
evenor :  (x : ℕ)  → Bool 
evenor zero = {! !}
evenor (suc x) = {!   !}
p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 x y = 
  x + (y + zero) + x 
  ≡⟨  comm+ (x + (y + 0)) x  ⟩
  x + (x + (y + zero))
  ≡⟨  cong (λ a → x + ( x + a)) (comm+ y 0 )⟩
  x + (x + y)
  ≡⟨  sym (assoc+ x x y) ⟩
  x + x + y
  ≡⟨  sym (cong (λ a → x + a + y ) (idr+ x )) ⟩  --x + x + y
  refl

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 a b =
  a + a + b + a * 0
  ≡⟨ cong (λ x → a + a + b + x) (comm* a 0) ⟩
  a + a + b + 0
  ≡⟨ idr+ (a + a + b) ⟩
  a + a + b
  ≡⟨ cong (λ x → a + x + b) (sym (idr+ a)) ⟩
  a + (a + 0) + b ∎

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 a b c =
  c * (b + 1 + a)
  ≡⟨ dist*+ c (b + 1) a ⟩
  c * (b + 1) + c * a
  ≡⟨ cong (_+ c * a) (dist*+ c b 1) ⟩
  c * b + c * 1 + c * a
  ≡⟨ comm+ (c * b + c * 1) (c * a) ⟩
  c * a + (c * b + c * 1)
  ≡⟨ cong₃ (λ x y z → x + (y + z)) (comm* c a) (comm* c b) (idr* c) ⟩
  a * c + (b * c + c)
  ≡⟨ sym (assoc+ (a * c) (b * c) c) ⟩
  a * c + b * c + c ∎

-- \==n = ≢
-- x ≢ y = ¬ (x ≡ y) = (x ≡ y) → ⊥

p9' : 0 ≢ the ℕ 1
p9' ()

p9 : 2 * 2 ≢ 3 * 1
p9 ()

-- Egyszerűbb, amikor mondani kell egy ellenpéldát:
p10 : ¬ ((n : ℕ) → n + 2 ≡ n + 1)
p10 f with f 0
... | ()

p10' : ¬ ((n : ℕ) → n + 2 ≡ n + 1)
p10' x with x 1 
... | ()

suc-inj : {x y : ℕ} → suc x ≡ suc y → x ≡ y
suc-inj refl = refl

-- ...mintsem bizonyítani, hogy ez a kettő sosem lesz egyenlő:
p11 : (n : ℕ) → n + 2 ≢ n + 1
p11 (suc n) e = p11 n (suc-inj e)

-- Mókásabb helyzet.
p11'' : ¬ Σ ℕ (λ n → n + 3 ≡ n + 1)
p11'' = f p11' where
  f : ((n : ℕ) → n + 3 ≢ n + 1) → ¬ Σ ℕ (λ n → n + 3 ≡ n + 1)
  f h (n , e) = h n e
  p11' : (n : ℕ) → n + 3 ≢ n + 1
  p11' (suc n) e = p11' n (suc-inj e)

p12 : ¬ Σ ℕ (λ n → n + n ≡ 3)
p12 (suc (suc (suc zero)) , ())
p12 (suc (suc (suc (suc n))) , ())

*2 : (a b : ℕ) → (a * b) + (a * b) ≡ 2 * a * b
*2 a b = sym (trans (comm* (a + (a + zero)) b) (trans (dist*+  b a (a + zero)) (trans (cong (λ x → b * a + b * x) (idr+ a)) (cong (λ x → x + x) (comm* b a)))))

[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 m n = 
  (m + n) * (m + n)
  ≡⟨ dist*+ (m + n) m n  ⟩
  (m + n) * m + (m + n) * n
  ≡⟨ cong (λ x → x + (m + n) * n) (comm* (m + n ) m)  ⟩
  m * (m + n) + (m + n) * n
  ≡⟨ cong (λ x → x + (m + n) * n)   (dist*+ m m n)  ⟩
  m * m + m * n + (m + n) * n
  ≡⟨ cong (m * m + m * n +_) (comm* (m + n ) n)  ⟩
  m * m + m * n + n * (m + n)
  ≡⟨ cong (λ x → m * m + m * n  + x)   (dist*+ n m n)  ⟩
    m * m + m * n + (n * m + n * n)
  ≡⟨ cong  (λ x → m * m + m * n + (x + n * n) ) (comm* n m)  ⟩
  m * m + m * n + (m * n + n * n)
  ≡⟨ ( (assoc+ (m * m) (m * n) (m * n + n * n)))  ⟩
  m * m + (m * n + (m * n + n * n))
  ≡⟨ cong (m * m +_) (sym (assoc+ (m * n) (m * n) ( n * n))) ⟩
  m * m + (m * n + m * n + n * n)
  ≡⟨ cong (λ x → m * m + (x + n * n)) (*2 m n) ⟩
  m * m + ((m + (m + zero)) * n + n * n)
  ≡⟨ sym (assoc+ (m * m) ((m + (m + zero)) * n) (n * n) )⟩
  m * m + (m + (m + zero)) * n + n * n ∎ 
  
{-
infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero  = 1
x ^ suc n = x * x ^ n
-}
p^2 : (a : ℕ) → a ^ 2 ≡ a * a 
p^2 a = cong (a *_) (idr* a)
p1 : (a b : ℕ) → (a + b) ^ 2 ≡ a ^ 2 + 2 * a * b + b ^ 2
p1 a b =
   (a + b) ^ 2
  ≡⟨ p^2 (a + b) ⟩
   (a + b) * (a + b)
  ≡⟨ [m+n]^2=m^2+2mn+n^2 a b ⟩
  a * a + 2 * a * b + b * b
  ≡⟨ sym (cong (λ x → a * a + 2 * a * b + x) (p^2 b)) ⟩
  a * a + 2 * a * b + b ^ 2
  ≡⟨ sym (cong (λ x → x + 2 * a * b + b ^ 2) (p^2 a)) ⟩
  a ^ 2 + 2 * a * b + b ^ 2 ∎ 

*0 : (a : ℕ) → a * 0 ≡ 0
*0 zero = refl
*0 (suc a) = *0 a

0^ : (n : ℕ) → 0 ^ (suc n) ≡ 0
0^ n = refl

^0 : (a : ℕ) → a ^ 0 ≡ 1
^0 a = refl

1^ : (n : ℕ) → 1 ^ n ≡ 1
1^ zero = refl
1^ (suc n) = trans (idr+  (1 ^ n)) (1^ n) 

^1 : (a : ℕ) → a ^ 1 ≡ a
^1 zero = refl
^1 (suc a) = cong suc (^1 a)

^+ : (a m n : ℕ) → a ^ (m + n) ≡ a ^ m * a ^ n
^+ a zero n = sym (idr+ (a ^ n))
^+ a (suc m) n = sym (trans (assoc* a  (a ^ m) (a ^ n)) (cong (λ x → a * x) (sym (^+ a m n))))


1*m : (m : ℕ) → 1 * m ≡ m 
1*m zero = refl
1*m (suc m) = cong suc (idr+ m)
m*1 : (m : ℕ) → m * 1 ≡ m 
m*1 zero = refl
m*1 (suc m) = cong suc (m*1 m)
-- dist+*ℕ : (m n o : ℕ) → (m + n) * o ≡ℕ m * o + n * o
-- comm+ℕ : (m n : ℕ) → m + n ≡ℕ n + m
-- comm*ℕ : (m n : ℕ) → m * n ≡ℕ n * m
-- m*n+m≡m* : (m n : ℕ) →  m * (suc n) ≡ m * n + m
-- m*n+m≡m* m zero = sym (trans (cong (λ x → x + m) (*0 m)) (sym (m*1 m)))
-- m*n+m≡m* m (suc n) = sym (trans (cong (λ x → m * suc n + x) (sym (1*m m))) (sym (trans (m*n+m≡m* m (suc n)) (cong (λ x → m * suc n + x) (sym (idr+ m))))) ) -- m * suc n + (m + zero) ≡ m * suc (suc n)

^* : (a m n : ℕ) → a ^ (m * n) ≡ (a ^ m) ^ n
^* a zero n = sym (1^ n)
^* a (suc m) zero = trans (cong (λ x → a ^ x) (*0 m)) refl
^* a (suc m) (suc n) =
  a * a ^ (n + m * suc n)
  ≡⟨ cong (a *_) (^+ a n (m * suc n))  ⟩
  a * (a ^ n * a ^ (m * suc n))
  ≡⟨ cong (λ x → a * ( a ^ n * x ) ) (^* a m (suc n))  ⟩
  a * (a ^ n * (a ^ m * (a ^ m) ^ n))
  ≡⟨ cong (λ x → a * ( a ^ n * (a ^ m * x) ) ) (sym (^* a m n))  ⟩
  a * (a ^ n * (a ^ m * a ^ (m * n)))
  ≡⟨ cong (a *_) (sym (assoc* (a ^ n) (a ^ m) (a ^ (m * n))))  ⟩
  a * (a ^ n * a ^ m * a ^ (m * n))
  ≡⟨ cong (λ x → a * (x * a ^ (m * n))) (comm* (a ^ n) (a ^ m))  ⟩
  a * (a ^ m * a ^ n * a ^ (m * n))
  ≡⟨ cong (a *_) (assoc* (a ^ m) (a ^ n) (a ^ (m * n)))  ⟩
  a * (a ^ m * (a ^ n * a ^ (m * n)))
  ≡⟨ cong (λ x → a * (a ^ m * (a ^ n * x))) (^* a m n)  ⟩
  a * (a ^ m * (a ^ n * (a ^ m) ^ n))
  ≡⟨ sym (assoc* a (a ^ m) (a ^ n * (a ^ m) ^ n))  ⟩
  a * a ^ m * (a ^ n * (a ^ m) ^ n)
  ≡⟨ cong (λ x → a * a ^ m * (a ^ n * x)) (sym (^* a m n)) ⟩
  a * a ^ m * (a ^ n * a ^ (m * n))
  ≡⟨ cong (a * a ^ m *_) (sym (^+ a n (m * n))) ⟩
  a * a ^ m * a ^ (n + m * n)
  ≡⟨ cong (a ^ suc m *_) (^* a (suc m) n)  ⟩
  a ^ suc m * (a ^ suc m) ^ n ∎ --a * a ^ m * (a * a ^ m) ^ n


*^ : (a b n : ℕ) → (a * b) ^ n ≡ a ^ n * b ^ n
*^ a b zero = refl
*^ a b (suc n) =
  a * b * (a * b) ^ n
  ≡⟨ cong (a * b *_)   (*^ a b n)  ⟩
  a * b * (a ^ n * b ^ n)
  ≡⟨ assoc* a b  (a ^ n * b ^ n)  ⟩
  a * (b * (a ^ n * b ^ n))
  ≡⟨ cong (a *_) (sym ((assoc* b  (a ^ n) (b ^ n) )))  ⟩
  a * (b * a ^ n * b ^ n)
  ≡⟨ cong (λ x → a * (x * b ^ n) ) (comm* b (a ^ n))  ⟩
  a * (a ^ n * b * b ^ n)
  ≡⟨ cong (a *_) (assoc* (a ^ n) b (b ^ n))  ⟩
    a * (a ^ n * (b * b ^ n))
  ≡⟨ sym (assoc* a (a ^ n) (b * b ^ n))  ⟩
  a * a ^ n * (b * b ^ n) ∎

p8 : (x y z : ℕ) → (27 ^ x) ^ y * 9 ^ z ≡ 3 ^ (3 * x * y + 2 * z)
p8 x y z =
   ((3 ^ 3)  ^ x) ^ y * (3 ^ 2) ^ z
   ≡⟨ cong (λ x  → x ^ y * (3 ^ 2) ^ z) (sym (^* 3 3 x))  ⟩
   ((3 ^ (3 * x))) ^ y * (3 ^ 2) ^ z
      ≡⟨ cong (λ x  → x  * (3 ^ 2) ^ z) (sym (^* 3 (3 * x) y))  ⟩
   (3 ^ (3 * x * y)) * (3 ^ 2) ^ z
   ≡⟨ cong (λ a → (3 ^ (3 * x * y)) * a) (sym (^* 3 2 z))  ⟩
   3 ^ (3 * x * y) * 3 ^ (2 * z)
   ≡⟨ sym (^+ 3 (3 * x * y) (2 * z))  ⟩
   3 ^ (3 * x * y + 2 * z)  ∎


ph3 : 10 * 10 ≡ 100
ph3 = refl
ph1 : 2 * 5 ≡ 10 * 1
ph1 = refl
ph2 : (a : ℕ ) → a + 1 ≡ suc a 
ph2 zero = refl
ph2 (suc a) = cong suc (ph2 a) 
-- ph4 : (a b : ℕ) → a * b * 0 ≡ 0
-- ph4 a b = {!   !}
p5 : (a : ℕ) → (10 * a + 5) ^ 2 ≡ a * (suc a) * 100 + 25
p5 a = 
  (10 * a + 5) ^ 2
  ≡⟨ p^2 (10 * a + 5)   ⟩
  (10 * a + 5) * (10 * a + 5)
   ≡⟨ [m+n]^2=m^2+2mn+n^2 (10 * a) 5  ⟩
  10 * a * (10 * a) + 2 * (10 * a) * 5 + 5 * 5
   ≡⟨  cong (λ x → 10 * a * (10 * a) + x * 5 + 5 * 5) ((comm* 2 (10 * a))) ⟩ -- sym (cong (λ x → x + 5 * 5) (dist+*  ((10 * a)) {!   !} (10 * a)))
  10 * a * (10 * a) + 10 * a * 2 * 5 + 5 * 5
   ≡⟨ cong (λ x → 10 * a * (10 * a) + x + 5 * 5) (assoc* (10 * a) 2 5) ⟩
  10 * a * (10 * a) + 10 * a * (2 * 5) + 5 * 5
   ≡⟨ cong (λ x → x + 5 * 5) (sym (dist*+ (10 * a) (10 * a) (2 * 5))) ⟩ 
  10 * a * (10 * a + 2 * 5) + 5 * 5
   ≡⟨ cong (λ x → 10 * a * (10 * a + x) + 5 * 5) ph1 ⟩
   10 * a * (10 * a + 10 * 1) + 5 * 5
      ≡⟨ cong (λ x → 10 * a * x + 5 * 5) (sym (dist*+ 10 a 1)) ⟩
   10 * a * (10 * (a + 1)) + 5 * 5
      ≡⟨ cong (λ x → 10 * a * (10 * x) + 5 * 5) (ph2 a) ⟩
   10 * a * (10 * suc a) + 5 * 5
        ≡⟨ cong (λ x →  x + 5 * 5) (sym (assoc* (10 * a) 10 (suc a))) ⟩
   10 * a * 10 * suc a + 5 * 5
    ≡⟨ cong (λ x → x  * 10 * suc a + 5 * 5) (comm* 10 a ) ⟩
   a * 10 * 10 * suc a + 5 * 5
           ≡⟨ cong (λ x → x * suc a + 5 * 5) (assoc* a 10 10) ⟩
   a * (10 * 10) * suc a + 5 * 5
   ≡⟨ cong (λ x → a * x * suc a + 5 * 5) ph3 ⟩
   a * 100 * suc a + 25
              ≡⟨ cong (λ x → x + 5 * 5) (assoc* a (100) (suc a)) ⟩
   a * (100 * suc a) + 25
      ≡⟨ cong (λ x →  a * x + 5 * 5) (comm* 100 (suc a)) ⟩
   a * (suc a * 100) + 5 * 5
    ≡⟨ cong ( λ x → x + 5 * 5)  (sym (assoc* a (suc a) 100)) ⟩
  a * (suc a) * 100 + 25 ∎

p6 : (a b c d e : ℕ) →
  (a + b) ^ 2 * 0 + (a * 0 + 0 + c * 0) ≡ 2 * d * 0 + e * (suc e) * 0 + ((a + 0) * 0)
p6 a b c d e = 
  (a + b) ^ 2 * 0 + (a * 0 + 0 + c * 0)
  ≡⟨ cong (λ x → x + (a * 0 + 0 + c * 0))  (nullr* ((a + b) ^ 2))  ⟩
  0 + (a * 0 + 0 + c * 0)
  ≡⟨ cong (λ x → 0 + (x + 0 + c * 0)) (nullr* a)  ⟩
      0 + (0 + 0 + c * 0)
  ≡⟨ cong (λ x → 0 + (0 + 0 + x)) (nullr* c)  ⟩
  0
  ≡⟨ sym (nullr* (a + 0))  ⟩
  (a + 0) * 0
  ≡⟨ sym  (cong (λ x → 0 + x +  (a + 0) * 0)  (nullr*  (e * suc e )))  ⟩
  0 + e * suc e * 0 + (a + 0) * 0
    ≡⟨ sym ( cong (λ x → x + e * (suc e) * 0 + ((a + 0) * 0))  (nullr* (2 * d )))  ⟩
  2 * d * 0 + e * (suc e) * 0 + ((a + 0) * 0) ∎


ph7 : (a : ℕ) → 3 * a ≡ a + a + a 
ph7 a = sym (trans (assoc+ a a a) (cong (λ x → a + (a + x)) (sym ((idr+ a ))))) -- trans (cong (λ x → a + x) {!   !}) {!   !}
ph8 : (a b : ℕ ) → b + a + b + a + b + a ≡ b + a + (b + a) + (b + a) 
ph8 a b = 
  b + a + b + a + b + a
    ≡⟨ cong (λ x → x + a + b + a) (assoc+ b a b) ⟩ 
    b + (a + b) + a + b + a
    ≡⟨ cong (λ x → x + b + a) (assoc+ b (a + b) a) ⟩ 
    b + (a + b + a) + b + a
    ≡⟨ cong (λ x → b + x + b + a) (assoc+ a b a) ⟩ 
    b + (a + (b + a)) + b + a
    ≡⟨ cong (λ x → x + a) (assoc+ b (a + (b + a)) b) ⟩ 
    b + (a + (b + a) + b) + a
    ≡⟨ assoc+ b (a + (b + a) + b) a ⟩ 
    b + (a + (b + a) + b + a)
    ≡⟨ cong (λ x → b + (x +  a) ) (assoc+ a (b + a ) b) ⟩ 
    b + (a + (b + a + b) + a)
     ≡⟨ cong (λ x → b + x) (assoc+ a  (b + a + b)  a) ⟩
    b + (a + (b + a + b + a))
    ≡⟨ cong (λ x → b + (a + x))  ( (assoc+ (b + a) b a )) ⟩ 
    b + (a + ((b + a) + (b + a)))
    ≡⟨ cong (λ x → b + x) (sym (assoc+ a (b + a) (b + a))) ⟩
    b + (a + (b + a) + (b + a))
    ≡⟨ sym ( assoc+ b (a + (b + a)) (b + a)) ⟩
    b + (a + (b + a)) + (b + a)
    ≡⟨ cong (λ x → x + (b + a)) (sym (assoc+ b a (b + a))) ⟩
    b + a + (b + a) + (b + a)    
    ∎
  --sym {!  cong (λ x →  x + (b + a) ) (comm+ (b + a) (b + a))  !}

p7 : (a b : ℕ) → b + a + b + a + b + a ≡ 3 * (b + 0 + a) * 1
p7 a b = 
  b + a + b + a + b + a
  ≡⟨ ph8 a b ⟩
    (b + a) + (b + a) + (b + a)
  ≡⟨ refl  ⟩
    b + a + (b + a) + (b + a)
  ≡⟨ sym ((ph7 (  b + a)))  ⟩
    3 * (b + a)
  ≡⟨ sym (cong (λ x → x) (idr* (3 * (b + a) )))  ⟩
    3 * (b + a) * 1
  ≡⟨ sym (cong (λ x → 3 * (x + a) * 1 ) (idr+ b))  ⟩
  3 * (b + 0 + a) * 1  ∎


task1 : ¬ ((n : ℕ) → n ≡ 3)
task1 x with x 1 
... | ()

task2 : {n : ℕ} → n ≡ 3 → n ≢ 10
task2 refl ()

invsuc : ℕ → ℕ 
invsuc zero = 1003
invsuc (suc n) = n

-- prove it without pattern matching on e! (hint: use pred)
suc≠zero : (n : ℕ ) → (suc n ≡ zero) → ⊥ 
suc≠zero n () 

sucinj' : (m n : ℕ) → ℕ.suc m ≡ suc n → m ≡ n --ℕ.'s suc 
sucinj' m n x = cong invsuc x

n≠sucn' : (n : ℕ) → n ≢ suc n
n≠sucn' zero ()
n≠sucn' (suc n) x = n≠sucn' n (sucinj' n (suc n) x)

task3 : ∀ n → Σ ℕ (n ≢_)
task3 n = (suc n) , n≠sucn' n --(n≠sucn')

task4 : Σ ℕ (λ n → ∀ m → n ≢ suc m)
task4  = zero , (λ m x → suc≠zero m (sym x))

p13' : ¬ Σ ℕ (λ n → ∀ x → x + suc n ≡ x)
p13' (n , p) with p 1 
... | ()

p14 : ¬ ((n k : ℕ) → 2 ^ suc n ≡ 3 ^ suc k)
p14 x with x 1 2 
... | ()

p15 : (n k : ℕ) → 2 ^ suc n ≢ 3 ^ suc k
p15 = {!   !}
 