-- (x + y) ^ 2 = x^2+2xy+_y^2

-- semiring = rig, rng
-- felgyuru

open import Lib

-- equational reasoning

-- trans (idr+ (a + 0)) (idr+ a)
e : (a : ℕ) → (a + 0) + 0 ≡ a
e a =
  (a + 0) + 0
                  ≡⟨ idr+ (a + 0) ⟩
  a + 0
                  ≡⟨ idr+ a ⟩
  a
                  ∎

record AbelianGroup (Car : Set) : Set where -- egysegelemes felcsoport
  field      -- Car is the carrier
    unit : Car
    op   : Car → Car → Car
    left-unit : (c : Car) → op unit c ≡ c
    assoc : (c c' c'' : Car) → op (op c c') c'' ≡ op c (op c' c'')
    inv   : Car → Car
    invl  : (c : Car) → op (inv c) c ≡ unit
    abel  : (c c' : Car) → op c c' ≡ op c' c
open AbelianGroup

Ab : (A : Set)(a : A) → AbelianGroup (a ≡ a)
unit (Ab A a) = refl
op (Ab A a) = trans
left-unit (Ab A a) = λ { refl → refl }
assoc (Ab A a) = λ { c c' refl → refl }
inv (Ab A a) = sym
invl (Ab A a) = λ { refl → refl }
abel (Ab A a) = λ { refl refl → refl }
{-
A egy ter
a,b:A
a--->b-be menu ut

(f : [0,1] → A),   f 0 = a,  f 1 = b,     (f ■ g) i := (f (i*2), ha i<0.5
                                                       (g (i*2-1), ha i>=0.5
                                          sym f i = f (1-i)
                                          refl {a} i := a

-}

idr= : {A : Set}{a a' : A}(e : a ≡ a) → trans e refl ≡ e
idr= e = {!!}

--                         Car
record Groupoid (Ob : Set)(Hom : Ob → Ob → Set) : Set where -- egysegelemes felcsoport
  field      -- Car is the carrier
    unit : ∀{I} → Hom I I
    op   : ∀{I J K} → Hom J I → Hom K J → Hom K I
    left-unit : {I J : Ob}(c : Hom J I) → op unit c ≡ c
    assoc : ∀{I J K L}(c : Hom J I)(c' : Hom K J)(c'' : Hom L K) →
       op (op c c') c'' ≡ op c (op c' c'')
    inv   : ∀{I J} → Hom I J → Hom J I
    invl  : ∀{I J}(c : Hom I J) → op (inv c) c ≡ unit
open Groupoid

Group = Groupoid ⊤

eqGroupoid : (A : Set) → Groupoid A _≡_
unit (eqGroupoid A) = refl
op (eqGroupoid A) = λ { refl e → e }  -- f ∘ g = λx → f (g x)     f ; g = λ x → g (f x),  >>=,  |,  x.f
left-unit (eqGroupoid A) = λ _ → refl
assoc (eqGroupoid A) = λ { refl _ _ → refl }
inv (eqGroupoid A) = λ { refl → refl }
invl (eqGroupoid A) = λ { refl → refl }

-- induktiv tipusokra altalanossagban:
--   konstruktorok injektivek
--                 diszjunktak

data Tree (A : Set) : Set where
  node : A → (ℕ → Tree A) → Tree A
  leaf : Tree A

prednode : {A : Set} → Tree A → (ℕ → Tree A)
prednode (node a f) = f
prednode leaf = λ _ → leaf

injnode : ∀{A : Set}{f g}{a a' : A} → node a f ≡ node a' g → f ≡ g
injnode e = cong prednode e

prednode' : {A : Set} → Tree A → Maybe A
prednode' (node a f) = just a
prednode' leaf = nothing

prednode'' : {A : Set}(as : Tree A) → as ≢ leaf → A
prednode'' (node a f) ne = a
prednode'' leaf ne = exfalso (ne refl)

{-
fromMaybe : {A : Set} → Maybe A → A → A
fromMaybe (just a) _ = a
fromMaybe nothing  a = a
-}

injjust : {A : Set}{a a' : A} → just a ≡ just a' → a ≡ a'
injjust {a = a} e = cong (fromMaybe a) e

injnode' : ∀{A : Set}{f g}{a a' : A} → node a f ≡ node a' g → a ≡ a'
injnode' e = injjust (cong prednode' e)

congd : {A : Set}{B : A → Set}{a a' : A}(f : (x : A) → B x)(e : a ≡ a') →
  subst B e (f a) ≡ f a'
congd {A} {B} {a} {.a} f refl = refl

-- f ≡ f' → a ≡ a' → f a ≡ f' a'

injnode'' : ∀{A : Set}{f g}{a a' : A} → node a f ≡ node a' g → a ≡ a'
injnode'' e = {!(congd prednode'' e)!}

P : {A : Set} → Tree A → Set
P (node a f) = ⊤
P leaf = ⊥

disjTree : ∀{A : Set}{a : A}{f} → node a f ≢ leaf
disjTree e = cast (cong P e) tt

-- A allitas fuggetlen az Agdatol = sem A-nak, sem ¬ A-nak nincs eleme
-- ilyen allitasok: (⊥ ≡ Fin 0), (⊤ ⊎ ⊤ ≡ Bool),
--                  ((A : Set) → ¬ ¬ A → A), ((A : Set) → A ⊎ ¬ A),
--                  ((λ x → x) ≡ (λ x → x + 0)),
--                  ((n : ℕ) → xs !! n ≡ ys !! n) → xs ≡ ys
--                  ((f : (A : Set) → A → A) → (A : Set)(a : A) → f A a ≡ a),
--                  Agda-ra vonatkozó Gödel mondat
--                  kivalasztasi axioma
--                  Church thesis
--                  ((e e' : a ≡ b)) → e ≡ e'

-- kovetkezo ora 17 perccel rovidebb. sajnos nincs...


{-
-- alternative implementation of Vec?

{-
Taking the principle of excluded middle from the mathematician
would be the same, say, as proscribing the telescope to the as-
tronomer or to the boxer the use of his fists. To prohibit existence
statements and the principle of excluded middle is tantamount to
relinquishing the science of mathematics altogether.
-}

-- there exists irrational numbers a b s.t. a^b is rational.
-- (sqrt(2))^(log_2 9) = sqrt(9) = 3

-- negative translation
-}
