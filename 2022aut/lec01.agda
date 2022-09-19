{-
Tipuselmelet (Agda)

Kaposi Ambrus
docens
Prog.Nyelvek es Ford.Prog. Tanszek
akaposi.web.elte.hu

kerdezni kell

honlap

Neptun letszamnovelo party szerdan 15.30kor a szobamban (2-620)

kovetelmenyek (elrettentes)

letszam
korabbi eredmenyek
--------------------------------------
t : A
program : tipus
bizonyitas : allitas
NINCS : ∀x.Eq (x+2) 5
        (x : ℕ) → Eq (x + 2) 5
(1 + 1) : ℕ
if_then_else_ :

(λ b → if b then 1 else 3) : Bool → ℕ

int f(bool b) {
  if b then
    return 1
  else
    return 3
}

1 + 1 = 2 (futtatas)

(λ b → if b then 1 else 3) true = if true then 1 else 3 = 1

halmazelmelet    tipuselmelet
t ∈ A            t : A
python
3 ∈ ℕ            3 : ℕ
                 1' : ℝ

f : ℕ → ℚ

P={0,2,4,6,...}
Q={1,3,5,...}

H(P) = 2 ∈ P
H(Q) = 2 ∈ Q
H(p) igaz, H(Q) hamis, pedig P ≅ Q

Makkai Mihaly - tipuselmeletre epult: first order logic with dependent sorts
2006 Voevodsky, Awodey, ... Martin-Lof tipuselmeletet kiegeszitettek a univalence nevu axiomaval, P ≅ Q  -> P = Q,  homotopy type theory

∀n.n>3

tipuselmelet, tipusrendszerek elmelete
kapcsolodo targyak
halmazelmelet
fuggo tipusos nyelvek
--------------------------------------
fuggvenyek
- halmazelmeletben relaciok: (a,b) ∈ f  ∧   (a,b') ∈ f  → b=b'
- fekete doboz, applikacio jelolese

       
x:ℕ |-----|
--->|  f  |---> f(x) : Bool
    |-----|

f : ℕ → Bool

-}

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool

n : ℕ
n = 1 + 1
-- C-c C-n
-- 1 + 1 = 2

-- f : Bool → ℕ
-- f = (λ b → if b then 1 else 3)

add3 : ℕ → ℕ
-- add3 n = n + 3

-- add3 5 = 5 + 3 = 8

add3 = (λ n → n + 3)   -- add3(5)

-- beta redukcio
-- add3 5 = (λ n → n + 3) 5 = (n + 3)[n↦5] = 5 + 3 = 8
