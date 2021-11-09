module 2021aut.t2.gy07.logic where
open import lib

---------------------------------------------------------
-- logic
---------------------------------------------------------

¬' : Set → Set
¬' A = A → ⊥

postulate
  bot : ⊥

anything : {X Y : Set} → ¬ X → X → Y
anything {X} {Y} nx x =  exfalso (nx' x)
  where
    nx' : X → ⊥
    nx' = nx

ret : {X : Set} → X → ¬ ¬ X
ret {X} x = nnx
  where
    nnx : (X → ⊥) → ⊥
    nnx nx = nx x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun {X} {Y} nx⊎y x = case nx⊎y (λ nx → anything {X} {Y} nx x) (λ y → y)

-- De Morgan

dm1 dm1' : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = _,_
  ((λ xy → (λ x → xy (ι₁ x)) , λ y → xy (ι₂ y)))
  λ (nx , ny) → λ xy → case xy (λ x → nx x) λ y → ny y
dm1' = {!!}

dm2 dm2' : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = λ nxny → λ (x , y) → case nxny (λ nx → nx x) (λ ny → ny y)
dm2' = {!!}

dm2b dm2b' : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b {X} {Y} = λ n[dm2b] → n[dm2b] λ n[x,y] → let
    nx : X → ⊥
    nx = λ x → let
      x : X
      x = x
      y : Y
      y = {!!}
      [dm2b] : ¬ (X × Y) → ¬ X ⊎ ¬ Y
      [dm2b] = λ n[x,y] → let
        ny : Y → ⊥
        ny = λ y → let
          x : X
          x = x
          y : Y
          y = y
          [x,y] : X × Y
          [x,y] = x , y
          in n[x,y] [x,y]
        in ι₂ ny
      in n[dm2b] [dm2b]
  in ι₁ nx
-- Idea: Call the top level n[dm2b] twice
dm2b' = {!!}

-- stuff

nocontra nocontra' : {X : Set} → ¬ (X ↔ ¬ X)
nocontra {X} = λ (x→nx , nx→x) → let
  nx = λ x → let
    nx' = x→nx x
    in nx' x
  x = nx→x nx
  in nx x
-- Idea: When defining nx (and got an x), you can also define nx as `x→nx x`, and apply x on that
nocontra' = {!!}

¬¬invol₁ ¬¬invol₁' : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ {X} = _,_
  (λ nnnnx → let
    nnx = λ nx → let
      nnnx = λ nnx → nnx nx
      in nnnnx nnnx
    in nnx)
  λ nnx → λ nnnx → nnnx nnx
-- Idea: nnnx = λ nnx → bot
¬¬invol₁' = {!!}

¬¬invol₂ ¬¬invol₂' : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = _,_
  (λ nnnx → λ x → let
    nnx = λ nx → nx x
    bot = nnnx nnx
    in bot)
  λ nx → λ nnx → nnx nx
-- simple
¬¬invol₂' = ?

nnlem nnlem' : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem {X} = λ n[lem] → let
  nx = λ x → let
    [lem] = ι₁ x
    in n[lem] [lem]
  [lem] = ι₂ nx
  in n[lem] [lem]
-- Idea: Apply nlem twice
nnlem' = {!!}

nndnp nndnp' : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp {X} = λ n[nnx→x] → let
  [nnx→x] = λ nnx → let
    nx = λ x → let
      [nnx→x] = λ nnx → x
      in n[nnx→x] [nnx→x]
    bot = nnx nx
    x = exfalso bot
    in x
  in n[nnx→x] [nnx→x]
-- Idea: Use exfalso
nndnp' = {!!}

dec2stab dec2stab' : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab {X} = λ xnx → λ nnx → case xnx (λ x → x) λ nx → exfalso (nnx nx)
-- Exfalso again
dec2stab' = {!!}

-- the other direction does not hold, but (this is a bit tricky to read):

dnp2lem dnp2lem' : ({X : Set} → (¬ ¬ X → X)) → ({X : Set} → (X ⊎ ¬ X))
dnp2lem dnp {X} = dnp {X ⊎ (X → ⊥)} λ n[xnx] → n[xnx] (ι₁ (dnp {X} λ nx → n[xnx] (ι₂ nx)))
-- Hívjuk meg a dnp-t egy bonyolult X-ekkel, ha elakadunk
dnp2lem' dnp {X} = {!!}
