module hf05-part2 where

open import Lib hiding (raiseᵣ; raiseₗ)
open import Lib.Containers.Vector hiding (take; drop; replicate; splitAt; _[_]%=_; _[_]≔_)

{-
Definiáld a deletions függvény, amely kitöröl a vektorból egy darab
elemet az összes lehetséges módon.
-}
deletions : {A : Set}{n : ℕ} → Vec A {!!} → Vec {!!} {!!}
deletions = {!!}

deletions-test1 : deletions {ℕ} (1 ∷ 2 ∷ 3 ∷ []) ≡ (2 ∷ 3 ∷ []) ∷ (1 ∷ 3 ∷ []) ∷ (1 ∷ 2 ∷ []) ∷ []
deletions-test1 = refl

deletions-test2 : deletions (false ∷ true ∷ []) ≡ (true ∷ []) ∷ (false ∷ []) ∷ []
deletions-test2 = refl

deletions-test3 : deletions {ℕ} (9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ []) ≡
  (8 ∷ 7 ∷ 6 ∷ 5 ∷ []) ∷
  (9 ∷ 7 ∷ 6 ∷ 5 ∷ []) ∷
  (9 ∷ 8 ∷ 6 ∷ 5 ∷ []) ∷
  (9 ∷ 8 ∷ 7 ∷ 5 ∷ []) ∷
  (9 ∷ 8 ∷ 7 ∷ 6 ∷ []) ∷ []
deletions-test3 = refl

{-
Definiáld az insertions függvényt, amely egy darab elemet egy vektorba az összes
lehetséges módon beilleszt!
-}
insertions : {A : Set}{n : ℕ} → A → Vec A {!!} → Vec {!!} {!!}
insertions = {!!}

insertions-test1 : insertions {ℕ} 0 (1 ∷ 2 ∷ 3 ∷ []) ≡
  (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷
  (1 ∷ 0 ∷ 2 ∷ 3 ∷ []) ∷
  (1 ∷ 2 ∷ 0 ∷ 3 ∷ []) ∷
  (1 ∷ 2 ∷ 3 ∷ 0 ∷ []) ∷ []
insertions-test1 = refl

insertions-test2 : insertions true (false ∷ []) ≡ (true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷ []
insertions-test2 = refl

insertions-test3 : insertions {ℕ} 10 (9 ∷ 11 ∷ 3 ∷ 0 ∷ []) ≡
  (10 ∷ 9 ∷ 11 ∷ 3 ∷ 0 ∷ []) ∷
  (9 ∷ 10 ∷ 11 ∷ 3 ∷ 0 ∷ []) ∷
  (9 ∷ 11 ∷ 10 ∷ 3 ∷ 0 ∷ []) ∷
  (9 ∷ 11 ∷ 3 ∷ 10 ∷ 0 ∷ []) ∷
  (9 ∷ 11 ∷ 3 ∷ 0 ∷ 10 ∷ []) ∷ []
insertions-test3 = refl

-- NEHÉZ FELADAT
{-
Definiáld a permutations függvényt, amely egy vektor összes lehetséges
permutációját megadja!
-}
permutations : {A : Set}{n : ℕ} → Vec A {!!} → Vec {!!} {!!}
permutations = {!!}

permutations-test1 : permutations {ℕ} (1 ∷ 2 ∷ 3 ∷ []) ≡
  (1 ∷ 2 ∷ 3 ∷ []) ∷
  (2 ∷ 1 ∷ 3 ∷ []) ∷
  (2 ∷ 3 ∷ 1 ∷ []) ∷
  (1 ∷ 3 ∷ 2 ∷ []) ∷
  (3 ∷ 1 ∷ 2 ∷ []) ∷
  (3 ∷ 2 ∷ 1 ∷ []) ∷ []
permutations-test1 = refl

permutations-test2 : permutations {ℕ} (2 ∷ 2 ∷ 9 ∷ 1 ∷ []) ≡
  (2 ∷ 2 ∷ 9 ∷ 1 ∷ []) ∷
  (2 ∷ 2 ∷ 9 ∷ 1 ∷ []) ∷
  (2 ∷ 9 ∷ 2 ∷ 1 ∷ []) ∷
  (2 ∷ 9 ∷ 1 ∷ 2 ∷ []) ∷
  (2 ∷ 9 ∷ 2 ∷ 1 ∷ []) ∷
  (9 ∷ 2 ∷ 2 ∷ 1 ∷ []) ∷
  (9 ∷ 2 ∷ 2 ∷ 1 ∷ []) ∷
  (9 ∷ 2 ∷ 1 ∷ 2 ∷ []) ∷
  (2 ∷ 9 ∷ 1 ∷ 2 ∷ []) ∷
  (9 ∷ 2 ∷ 1 ∷ 2 ∷ []) ∷
  (9 ∷ 1 ∷ 2 ∷ 2 ∷ []) ∷
  (9 ∷ 1 ∷ 2 ∷ 2 ∷ []) ∷
  (2 ∷ 2 ∷ 1 ∷ 9 ∷ []) ∷
  (2 ∷ 2 ∷ 1 ∷ 9 ∷ []) ∷
  (2 ∷ 1 ∷ 2 ∷ 9 ∷ []) ∷
  (2 ∷ 1 ∷ 9 ∷ 2 ∷ []) ∷
  (2 ∷ 1 ∷ 2 ∷ 9 ∷ []) ∷
  (1 ∷ 2 ∷ 2 ∷ 9 ∷ []) ∷
  (1 ∷ 2 ∷ 2 ∷ 9 ∷ []) ∷
  (1 ∷ 2 ∷ 9 ∷ 2 ∷ []) ∷
  (2 ∷ 1 ∷ 9 ∷ 2 ∷ []) ∷
  (1 ∷ 2 ∷ 9 ∷ 2 ∷ []) ∷
  (1 ∷ 9 ∷ 2 ∷ 2 ∷ []) ∷
  (1 ∷ 9 ∷ 2 ∷ 2 ∷ []) ∷ []
permutations-test2 = refl

-- NEHÉZ FELADAT
-- Probléma lesz bárhogyan is, új ötlet kell.
{-
Definiáld a reverse függvényt, amely egy vektor elemeinek a sorrendjét megfordítja.
Megj.: A naív definíció önmagában nem működik.
-}

reverse : {A : Set}{n : ℕ} → Vec A n → Vec A n
reverse = {!!}

{-
Bizonyítsd be, hogy a Fin 2 típus izomorf a Bool típussal!
-}
Fin2↔Bool : Fin 2 ↔ Bool
Fin2↔Bool = {!!}

Fin2-proof1 : ∀ x → fst Fin2↔Bool (snd Fin2↔Bool x) ≡ x
Fin2-proof1 false = refl
Fin2-proof1 true = refl

Fin2-proof2 : ∀ x → snd Fin2↔Bool (fst Fin2↔Bool x) ≡ x
Fin2-proof2 fzero = refl
Fin2-proof2 (fsuc fzero) = refl

{-
Definiáld a raiseᵣ, raiseₗ függvényeket, amelyek jobbról, illetve balról
növelik a Fin szintjét.
-}
raiseᵣ : {m : ℕ}(n : ℕ) → Fin m → Fin (n + m)
raiseᵣ = {!!}

raiseₗ : {m : ℕ} → Fin m → (n : ℕ) → Fin (m + n)
raiseₗ = {!!}

{-
Bizonyítsd be, hogy a Fin n ⊎ Fin m izomorf Fin (n + m)-mel.

Megj.: Nem tudtam hozzá jó tesztet írni, mert nem triviális
       bizonyítani, hogy oda-vissza és vissza-oda is identitás lesz.
-}
FinIso : {n m : ℕ} → Fin n ⊎ Fin m ↔ Fin (n + m)
FinIso = {!!}

{-
Definiáld az insertAt függvényt, amely egy elemet egy adott indexű
helyre beszúr. A vektort ne lehessen alulindexelni, illetve egynél többel
túlindexelni se. (Az eggyel való túlindexelés lesz a vektor utolsó utáni eleme,
ha oda szeretnénk az elemet beszúrni.)
-}

insertAt : {A : Set}{n : ℕ} → Fin {!!} → A → Vec A {!!} → Vec A {!!}
insertAt = {!!}

insertAt-test1 : insertAt {ℕ} fzero 0 (1 ∷ 2 ∷ []) ≡ 0 ∷ 1 ∷ 2 ∷ []
insertAt-test1 = refl

insertAt-test2 : insertAt {ℕ} (fsuc fzero) 0 (1 ∷ 2 ∷ []) ≡ 1 ∷ 0 ∷ 2 ∷ []
insertAt-test2 = refl

insertAt-test3 : insertAt {ℕ} (fsuc (fsuc fzero)) 0 (1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 0 ∷ []
insertAt-test3 = refl

insertAt-test4 : insertAt fzero true (false ∷ false ∷ false ∷ []) ≡ true ∷ false ∷ false ∷ false ∷ []
insertAt-test4 = refl

insertAt-test5 : insertAt (fsuc fzero) true (false ∷ false ∷ false ∷ []) ≡ false ∷ true ∷ false ∷ false ∷ []
insertAt-test5 = refl

insertAt-test6 : insertAt (fsuc (fsuc fzero)) true (false ∷ false ∷ false ∷ []) ≡ false ∷ false ∷ true ∷ false ∷ []
insertAt-test6 = refl

insertAt-test7 : insertAt (fsuc (fsuc (fsuc fzero))) true (false ∷ false ∷ false ∷ []) ≡ false ∷ false ∷ false ∷ true ∷ []
insertAt-test7 = refl
{-
Definiáld a removeAt függvényt, amely egy adott indexű helyről eltávolít
egy elemet.
-}

removeAt : {A : Set}{n : ℕ} → Fin {!!} → Vec A {!!} → Vec A {!!}
removeAt = {!!}

removeAt-test1 : removeAt {ℕ} fzero (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 2 ∷ 3 ∷ 4 ∷ []
removeAt-test1 = refl

removeAt-test2 : removeAt {ℕ} (fsuc fzero) (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 1 ∷ 3 ∷ 4 ∷ []
removeAt-test2 = refl

removeAt-test3 : removeAt {ℕ} (fsuc (fsuc fzero)) (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 1 ∷ 2 ∷ 4 ∷ []
removeAt-test3 = refl

removeAt-test4 : removeAt {ℕ} (fsuc (fsuc (fsuc fzero))) (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
removeAt-test4 = refl

{-
Definiáld a _[_]%=_ függvényt, amely egy adott indexű helyen
az elemet módosítja úgy, hogy egy adott függvényt meghív
az azon az indexű helyen lévő elemre!
-}

infixl 6 _[_]%=_

_[_]%=_ : {A : Set}{n : ℕ} → Vec A {!!} → Fin {!!} → (A → A) → Vec A {!!}
xs [ i ]%= f = {!!}

update-test1 : _[_]%=_ {ℕ} (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) fzero (10 *_) ≡ (10 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
update-test1 = refl

update-test2 : _[_]%=_ {ℕ} (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) (fsuc fzero) (10 *_) ≡ (1 ∷ 20 ∷ 3 ∷ 4 ∷ 5 ∷ [])
update-test2 = refl

update-test3 : _[_]%=_ {ℕ} (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) (fsuc (fsuc fzero)) (10 +_) ≡ (1 ∷ 2 ∷ 13 ∷ 4 ∷ 5 ∷ [])
update-test3 = refl

update-test4 : _[_]%=_ {ℕ} (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) (fsuc (fsuc (fsuc fzero))) (10 +_) ≡ (1 ∷ 2 ∷ 3 ∷ 14 ∷ 5 ∷ [])
update-test4 = refl

update-test5 : _[_]%=_ {ℕ} (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) (fsuc (fsuc (fsuc (fsuc fzero)))) (10 +_) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 15 ∷ [])
update-test5 = refl
{-
Definiáld a _[_]≔_ függvényt, amely egy adott indexű helyen lévő
elemet lecserél egy másik elemre!
-}

-- \:= = ≔
infixl 6 _[_]≔_

_[_]≔_ : {A : Set}{n : ℕ} → Vec A {!!} → Fin {!!} → A → Vec A {!!}
xs [ i ]≔ y = {!!}

updateValue-test1 : _[_]≔_ {ℕ} (1 ∷ 2 ∷ 9 ∷ []) fzero 0 ≡ 0 ∷ 2 ∷ 9 ∷ []
updateValue-test1 = refl

updateValue-test2 : _[_]≔_ {ℕ} (1 ∷ 2 ∷ 9 ∷ []) (fsuc fzero) 0 ≡ 1 ∷ 0 ∷ 9 ∷ []
updateValue-test2 = refl

updateValue-test3 : _[_]≔_ {ℕ} (1 ∷ 2 ∷ 9 ∷ []) (fsuc (fsuc fzero)) 0 ≡ 1 ∷ 2 ∷ 0 ∷ []
updateValue-test3 = refl

updateValue-test4 : (false ∷ false ∷ []) [ fsuc fzero ]≔ true ≡ false ∷ true ∷ []
updateValue-test4 = refl
