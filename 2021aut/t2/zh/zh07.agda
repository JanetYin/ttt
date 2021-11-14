module zh07 where
open import lib

task1 : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
task1 = _,_
  (λ nnnx → λ x → let
    nnx = λ nx → nx x
    bot = nnnx nnx
    in bot)
  λ nx → λ nnx → nnx nx
