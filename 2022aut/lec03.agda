open import lib hiding (_⊎_; case; _×_; _,_; ⊥; ⊤; tt)

g : (ℕ → ℕ) → (ℕ → ℕ) → _
g = λ f x → x (f (1 + x 3))

{-
(λ x → t) u = t[x↦u]


λ f x → x (f (1 + x 3))
          \___________/
            : ℕ
        \_____________/
          :ℕ

\_____________________/
   :(ℕ → ℕ) → (ℕ → ℕ) → ℕ

  f : ℕ → ℕ
  x : ℕ → ℕ
-}

{-
A → B
Nat, Bool

osszeg  A ⊎ B
- pelda: rendeles szama, felhasznalo azonositoszama, hiaba ugyanaz
- reprezentacio fuggetlenseg: A ∪ B vs. A ⊎ B
- case
-}
-- induktiv tipus
data _⊎_ (A B : Type) : Type where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

RendSzam = ℕ
FelhAzon = ℕ
Rendeles = RendSzam ⊎ FelhAzon
-- rendeleszam = 86425100
-- felhasznalo azonosito = 100

rend : Rendeles
rend = inj₁ 123 -- C-u C-u C-c C-,

-- ⊎ osszeg tipus, diszjunkt unio
-- unio gonosz, intenzionalis, reprezentacio-fuggo
-- {0,1,2} ∪ {0,3,4} = {0,1,2,3,4}
-- {0,1,2} ∪ {0,1,2} = {0,1,2}
-- {0,1,2} ⊎ {0,1,2} = {inj₁ 0, inj₁ 1, inj₁ 2, inj₂ 0, inj₂ 1, inj₂ 2}

case : {A B C : Type} → A ⊎ B → (A → C) → (B → _) → C
case (inj₁ a) f g = f a
case (inj₂ b) _ g = g b

{-
record ×
- copatternmatching constructor
- curry, uncurry, bebizonyitani, hogy izomorfizmus (η)
-}

-- koinduktiv tipus
record _×_ (A B : Type) : Type where field
  proj₁ : A
  proj₂ : B
open _×_

_,_ : {X Y : Type} → X → Y → X × Y
proj₁ (x , y) = x
proj₂ (x , y) = y

-- van η szabaly (surjective pairing):
-- w = proj₁ w , proj₂ w

curry : {A B C : Type} → (A × B → C) → A → B → C
curry f a b = f (a , b)

uncurry : {A B C : Type} → (A → B → C) → A × B → C
uncurry f w = f (proj₁ w) (proj₂ w)

postulate
  A B C : Type
  f : A → B → C
{-
altalanossagban, ha van A, B : Type, g : A → B, h : B → A, es
minden a-ra h (g a) = a es minden b-re g (h b) = b,
A es B izomorf, A es B bijekcioban van

curry (uncurry f) = (def)
λ a → λ b → uncurry f (a , b) =(def)
λ a → λ b → f (proj₁ (a , b)) (proj₂ (a , b)) =(proj₁ def)
λ a → λ b → f a (proj₂ (a , b)) =(proj₂ def)
λ a → (λ b → (f a) b) =(η)
      (λ x → t     x)
λ a → f a =(η)
f

uncurry (curry f) =(η)
λ w → uncurry (curry f) w =(uncurry def)
λ w → curry f (proj₁ w) (proj₂ w) =(curry def)
λ w → f (proj₁ w , proj₂ w) =(record η szabaly)
λ w → f w =(fuggveny η)
f
-}

-- ⊎ dualisa a szorzat

-- nullaris osszeg, nulla tipus
data ⊥ : Type where -- bottom, empty type, ures tipus \bot

case⊥ : {C : Type} → ⊥ → C
case⊥ ()

record ⊤ : Type where      -- \top

tt : ⊤
tt = record {}

-- ⊤ × A ≅ A
-- (A ⊎ B) ⊎ C ≅ A ⊎ (B ⊎ C)
-- C ^ (B × A) ≅ (C ^ B) ^ A

{-
⊤,⊥,𝟚,𝟛, hany eleme van a veges tipusoknak? fuggvenyek is

MAJD: nezzuk meg a tipusosztalyok implementaciojat Agdaban
MAJD: szorzat tipust data-val
-}

-- kovetkezo ora 4 perccel rovidebb lesz

