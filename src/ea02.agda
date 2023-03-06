open import lib hiding (_⊎_; inl; inr; case; ⊥; exfalso)

-- ez az ora 4 perccel rovidebb

-- kviz

twice : {X : Set} → (X → X) → X → X
twice f x = f (f x)

add2 : ℕ → ℕ
add2 x = x + 2

-- C-c C-d   deduce type

-- add2 : ℕ → ℕ
-- twice : {A : Set} → (A → A) → A → A
-- twice {ℕ} : (ℕ → ℕ) → ℕ → ℕ
-- (twice add2) 3
--        \___/ ‌\/       A := ℕ
--        :ℕ→ℕ   :ℕ
-- \__________/
--   : ℕ → ℕ
-- \____________/
--     : ℕ

-- twice (add2 3)
--       \______/
--         : ℕ
-- nincs olyan A, melyre (A → A) = ℕ

--  (λ f x → f (f x x) (x + 1))
--                     \_____/
--                      : ℕ
-- x : ℕ
-- f : ℕ → ℕ → ℕ
-- (ℕ → ℕ → ℕ) → ℕ → ℕ
-- (x : ℕ) → (y : ℕ) → ℕ  =  ℕ → ℕ → ℕ

----------------------------------------------
-- lambda kalkulus es veges tipusok
----------------------------------------------

-- eddig: →, ℕ, {A : Set} →

-- lambda kalkulus (tipusos), a termek kornyezetben, β, (λ x → (λ y → x + y)) y, α, η

-- termek vannak ebben a nyelvben
-- t ::= x | t t' | λ x → t
{-
kornyezet: megadja az osszes szabad valtozo tipusat

Γ = (x : ℕ, y : Bool, z : ℕ → Bool)  lista

Γ ⊢ t : A → B       Γ ⊢ t' : A                             Γ,x:A ⊢ t : B
------------------------------     ---------------    -----------------------
        Γ ⊢ t t' : B               Γ,x:A,Δ ⊢ x : A    Γ ⊢ (λ x → t) : (A → B)

β = termek kozti egyenloseg, ill. hogyan kell programokat futtatni

  (λ x → t) t' = t[x ↦ t']                                        <- altalanos szabaly

  (λ y → (1 + y) + y) 3  = ((1+y)+y)[y↦3] = (1+3)+3 = 7           <- a szabaly egyik esete
     ‌\/  \_________/  \/
      x        t       t'

  (λ x → x) 3 = x[x↦3] = 3
  (λ x → (λ x → x)) 3 = t[x↦t'] = (λ x → x)[x ↦ 3] =  ... problemas
         \_______/  t'
            t

  (λ x → (λ x → x)) 3 =(α) = (λ x → (λ y → y)) 3 = (λ y → y)[x ↦ 3] = λ y → y = λ x → x

α = λ altal kotott valtozok neve nem szamit, pl. (λ x → x) = (λ y → y) = (λ alma → alma)

int f(int x) {        int f(int y) {       <- koto operator a _(_), a kotes neve x/y, kotes hataskore fgv torzse
  return (x+x);   =      return (y+y);
}                     }              

for (int x = 0; x < 10; x++) {               for (int z = 0; z < 10; z++) {         <- for koto operator, kotes neve x/z, x, kotes hataskore a ciklus torzse
  y = x + y;                        =          y = z + y;                  
}                                            }

lim (1/x+2)   koto operator: lim, kotes neve x, kotes hataskore zarojelben levo resz, tovabbi parameter ∞
x↦∞

n
Σ (x+1/x)        koto operator: Σ, kotes neve x, tovabbi ket parameter: 0, n, kotes hataskore: zarojeles resz
x=0

n                              _
∫ x+1/x dx      koto operator: ∫_d_     kotes neve x (d utan van), kotes hataskore ∫ es d kozotti resz, tovabbi ket parameter
0                              _
    n
  = ∫ alma+1/alma dalma
    0

(λ x → t)         koto operator: λ, x kotott valtozo neve, kotes hataskore az a → utani resz, 

λ x → λ y → λ z → x + y - z + 2

λ x → λ x → x + x = λ x → λ y → y + y    elfedes

(λ x → (λ y → x + y)) y = (λ y → x + y)[x↦y] ≠ (λ y → y + y)     name capture (nev-elfogas)
                       (1)         ∥(α)      (2)   
                          (λ z → x + z)[x↦y] = (λ z → y + z)

nagyon figyelni kell, amikor az ember a _[_↦_] helyettesites operatort megadja

α, β, η

   f : A → B                       
---------------------η*      --------------------β*     --------------------------α*
  f = λ x → f x              (λ x → t) u = t[x↦u]       (λ x → t) = λ y → (t[x↦y])

(λ f x → f (f x)) (_+_ 1) 3         =(roviditett jeloles feloldasa)
((λ f → (λ x → f (f x))) (_+_ 1)) 3 =(β)
    x   \_____________/  \_____/
            t                u

(t[x↦u]) 3                      =(t,x,u feloldasa)
((λ x → f (f x))[f↦(_+_ 1)]) 3  =(helyettesites elvegzese)
((λ x → (_+_ 1) ((_+_ 1) x))) 3 =(rovidites feloldasa)
((λ x → (_+_ 1) (1 + x))) 3     =(rovidites feloldasa)                 _+_ 1 2 = 1 + 2 = 3
(λ x → 1 + (1 + x)) 3           =(β)
   x   \_________/  \/
           t        u
(1 + (1 + x))[x↦3]              =(helyettesites elvegzese)
(1 + (1 + 3))                   =(altalanos iskola)
5
-}

-- C-c C-n normalise, program futtatasa
















-- kombinator logika

-- t ::= t t' | S | K     K t t' = t       S t t' t'' = t t'' (t' t'')

K : {A B : Set} → A → B → A
K = λ a b → a  -- K t t' = ((λ a b → a) t) t' = t

S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S = λ f g a → f a (g a)   -- S t t' t'' = (λ f g a → f a (g a)) t t' t'' = t t'' (t' t'')

I : {A : Set} → A → A
I = λ a → a           -- megadhato S-el es K-val

-- (λ x → t)        ahol t-ben nincs λ, de van S, K, applikacio, valtozo
-- (λ x → x) := I
-- (λ x → y) := K y
-- (λ x → t t') := S (λ x → t) (λ x → t')
-- (λ x → K) := K K
-- (λ x → S) := K S

-- OPTIM: (λ x → t), ahol t-ben nincs x := K t
-- OPTIM: (λ x → t x) := t

-- _∘_ = λ f g x → f (g x) = λ f → λ g → (λ x → f (g x)) =
--                                              t \___/
--                                                 t'
--                                       \_____________/
-- λ f → λ g → (S (λ x → f) (λ x → g x)) =
-- λ f → λ g → (S (K f) (S (λ x → g) (λ x → x))) =
-- λ f → (λ g → (S (K f) (S (K g) I))) =
-- λ f → (λ g → ((S (K f)) (S (K g) I))) =
-- λ f → S (λ g → (S (K f))) (λ g → S (K g) I) =
-- λ f → S (K (S (K f))) (λ g → S (K g) I) =
-- λ f → S (K (S (K f))) (S (λ g → S (K g)) (K I)) =
-- λ f → S (K (S (K f))) (S (S (λ g → S) (λ g → K g)) (K I)) =
-- S (λ f → S (K (S (K f)))) (K (S (S (K S) K) (K I))) =
-- S (S (K S) (λ f → K (S (K f)))) (K (S (S (K S) K) (K I))) =
-- S (S (K S) (S (λ f → K) (λ f → S (K f)))) (K (S (S (K S) K) (K I))) =
-- S (S (K S) (S (K K) (S (K S) K))) (K (S (S (K S) K) (K I)))

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
_∘_ = S (S (K S) (S (K K) (S (K S) K))) (K (S (S (K S) K) (K I)))

-- comp :: (b -> c) -> (a -> b) -> a -> c

-- kovetkezo 5 perccel rovidebb



-- comnbinator conversion: (λ x → t) is converted by looking at t (which does not contain λ)
-- convert _∘_ into combinatory terms

-- ⊎, CustRef, OrdNum, ugyanaz a szam; ∪ vs. ⊎

-- ×, curry, uncurry, izomorfizmus

-- ⊤, ⊥, Bool=⊤+⊤

-- finite type isos




