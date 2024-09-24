module gy11 where

-- Proofs on other types (we can have proofs on other types as well, not just ℕ)

open import Lib

injL₂ : ∀{i}{A : Set i}{t t' : List A}{n : A} →  n ∷ t ≡ n ∷ t' → t ≡ t'
injL₂ proof = cong inverse proof
  where
    inverse : ∀{i}{A : Set i} → List A → List A 
    inverse [] = []
    inverse (x ∷ x₁) = x₁

List-idr++ : ∀{i}{A : Set i}(xs : List A) → let open List in xs ++ [] ≡ xs
List-idr++ {i} {A} [] = refl
List-idr++ {i} {A} (x ∷ xs) = cong (λ y → x ∷ y) (List-idr++ xs)
-- fincomm : (n k : ℕ) → Fin (n + k) → Fin (k + n)
-- -- END FIX
-- fincomm n k x = subst (Fin) (comm+ n k) x
vecst : ∀{i}{A : Set i}{n} → let open Vec in  Vec A n → Vec A (n + 0)
vecst {i} {A} {n} x = subst (Vec A) (sym (idr+ n)) x

Vec-idr++ : ∀{i}{A : Set i}{n}(xs : Vec A n) → let open Vec in xs ++ [] ≡  subst (Vec A) (sym (idr+ n)) xs --subst (Vec A) (sym (idr+ n))
Vec-idr++ {i} {A} {zero} [] = refl
Vec-idr++ {i} {A} {suc n} (x ∷ xs) = trans (cong  (x ∷_ ) (Vec-idr++ xs)) (trans (p1 {n}{n + zero} (sym (idr+ n)) x xs) (cong (λ a → subst (Vec A) a (x ∷ xs)) (sym (p2 suc (idr+ n) )))) -- x ∷ ? -- (Vec-idr++ {!   !})
    where 
        p1 :  {n k : ℕ} → (e : n ≡ k) → (x : A) → (xs : Vec A n) → x ∷ subst (Vec A) e xs ≡ subst (Vec A) (cong suc e) (x ∷ xs)
        p1 refl x xs = refl
        p2 :  {A : Set} → {n k : A} → (f : A → A) → (e : n ≡ k ) →  sym (cong f e) ≡ cong f (sym e)
        p2 f refl = refl

List-dist-length++ : ∀{i}{A : Set i}(xs ys : List A) → let open List in length (xs ++ ys) ≡ length xs + length ys
List-dist-length++ [] ys = refl
List-dist-length++ (x ∷ xs) ys = cong suc  (List-dist-length++ xs ys)

-- reverseNaive : ∀{i}{A : Set i} → List A → List A
-- reverseNaive [] = []
-- reverseNaive (x ∷ xs) = reverseNaive xs List.++ x ∷ []
-- reverse : ∀{i}{A : Set i} → List A → List A
-- reverse = foldl (λ acc b → b ∷ acc) []

-- foldl : ∀{i j}{A : Set i}{B : Set j} → (B → A → B) → B → List A → B
-- foldl f n []       = n
-- foldl f n (x ∷ xs) = foldl f (f n x) xs
-- List ++ is associative! State it and then prove it!

List-assoc++ : ∀{i}{A : Set i}(xs ys zs : List A) → let open List in (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
List-assoc++ {i} {A} [] ys zs = refl
List-assoc++ {i} {A} (x ∷ xs) ys zs = cong (x ∷_) (List-assoc++ {i} {A} xs ys zs)
 
reverse-gen : ∀{i}{A : Set i}(xs ys : List A) →  List.foldl (λ acc b → b ∷ acc)  ys xs ≡ List.foldl (λ acc b → b ∷ acc)  [] xs List.++ ys
reverse-gen {i} {A} [] ys = refl
reverse-gen {i} {A} (x ∷ xs) ys = trans (reverse-gen xs (x ∷ ys)) (trans (sym (List-assoc++ (List.reverse xs) (x ∷ []) ys)) (cong (λ a → a List.++ ys) (sym (reverse-gen xs (x ∷ [])))))

reverse-one : ∀{i}{A : Set i}(x : A)(xs : List A) → let open List in reverse (x ∷ xs) ≡ reverse xs ++ (x ∷ [])
reverse-one x xs = reverse-gen xs (x ∷ [])
dist-reverse++ : ∀{i}{A : Set i}(xs ys : List A) → let open List in reverse (xs ++ ys) ≡ reverse ys ++ reverse xs 
dist-reverse++ [] ys = reverse-gen ys []
dist-reverse++ (x ∷ xs) ys = trans (reverse-one x (xs List.++ ys)) (trans (cong ( λ a → a List.++ x ∷ []) (dist-reverse++ xs ys)) (trans (List-assoc++ (List.reverse ys) (List.reverse xs) (x ∷ [])) (cong (λ a → List.reverse ys List.++ a) (sym (reverse-one x xs)))))

reverse++-dist : ∀{i}{A : Set i}{xs ys : List A} → let open List in reverseNaive (xs ++ ys) ≡ (reverseNaive ys ++ reverseNaive xs)
reverse++-dist {i} {A} {[]} {ys} = sym (List-idr++  (List.reverseNaive ys))
reverse++-dist {i} {A} {x ∷ xs} {ys} = trans (cong (λ a → a List.++ x ∷ []) (reverse++-dist {i} {A} {xs} {ys})) (List-assoc++  (List.reverseNaive ys) (List.reverseNaive xs) (x ∷ []))
    where --123 321
        pp1 : ∀{i}{A : Set i}{x : A}{xs : List A} →  List.reverseNaive (x ∷ xs) ≡ List.reverseNaive xs List.++ (x ∷ []) 
        pp1 {i} {A} {x} {xs} = refl   
        
{-
Vec-idr++ : ∀{i}{A : Set i}{n}(xs : Vec A n) → let open Vec in xs ++ [] ≡  subst (Vec A) (sym (idr+ n)) xs --subst (Vec A) (sym (idr+ n))
Vec-idr++ {i} {A} {zero} [] = refl
Vec-idr++ {i} {A} {suc n} (x ∷ xs) = trans (cong  (x ∷_ ) (Vec-idr++ xs)) (trans (p1 {n}{n + zero} (sym (idr+ n)) x xs) (cong (λ a → subst (Vec A) a (x ∷ xs)) (sym (p2 suc (idr+ n) )))) -- x ∷ ? -- (Vec-idr++ {!   !})
    where 
        p1 :  {n k : ℕ} → (e : n ≡ k) → (x : A) → (xs : Vec A n) → x ∷ subst (Vec A) e xs ≡ subst (Vec A) (cong suc e) (x ∷ xs)
        p1 refl x xs = refl
        p2 :  {A : Set} → {n k : A} → (f : A → A) → (e : n ≡ k ) →  sym (cong f e) ≡ cong f (sym e)
        p2 f refl = refl
-}

vecsta : ∀{i}{A : Set i}{n} → let open Vec in  Vec A n → Vec A (n + 0)
vecsta {i} {A} {n} x = subst (Vec A) (sym (idr+ n)) x
-- Vec ++ associative! (This is hard to state and very difficult to prove!)
Vec-assoc++ : ∀{i}{A : Set i}{l m n : ℕ}{xs : Vec A l}{ys : Vec A m}{zs : Vec A n} → let open Vec in (xs ++ ys) ++ zs ≡ subst (Vec A) (sym (assoc+ l m n)) (xs ++ (ys ++ zs)) --xs ++ (ys ++ zs)
Vec-assoc++ {i} {A} {zero} {m} {n} {[]} {ys} {zs} = refl
Vec-assoc++ {i} {A} {suc l} {m} {n} {x ∷ xs} {ys} {zs} = trans (cong (x ∷_) (Vec-assoc++ {i} {A} {l} {m} {n} {xs} {ys} {zs})) (trans (p1 {l + (m + n)}{l + m + n} (sym (assoc+ l m n)) x (xs Vec.++ ys Vec.++ zs)) (cong (λ a → subst (Vec A) a (x ∷ xs Vec.++ ys Vec.++ zs)) (sym (p2 suc (assoc+ l m n)))))
    where 
        p1 :  {n k : ℕ} → (e : n ≡ k) → (x : A) → (xs : Vec A n) → x ∷ subst (Vec A) e xs ≡ subst (Vec A) (cong suc e) (x ∷ xs)
        p1 refl x xs = refl
        p2 :  {A : Set} → {n k : A} → (f : A → A) → (e : n ≡ k ) →  sym (cong f e) ≡ cong f (sym e)
        p2 f refl = refl
    --     x ∷
    --   subst (Vec A) (sym (assoc+ l m n)) (xs Vec.++ ys Vec.++ zs)
    --   ≡
    --   subst (Vec A) (sym (cong suc (assoc+ l m n)))
    --   (x ∷ xs Vec.++ ys Vec.++ zs)
------------------------------------------
-- How to model mathematical structures?
------------------------------------------

-- Different formalisations are possible.
-- e.g. we can encode the semigroup structure inside the record, not in the type.
-- Every form has its pros and cons.
-- In this formalisation the type and the operation is known at type level, we need to prove that the operation is associative.

-- State he associativity rule.
record Semigroup {i}{A : Set i}(_⊕_ : A → A → A) : Set i where
  field
    assoc : {x y z : A} → (x ⊕ y)  ⊕ z ≡ x ⊕ (y ⊕ z)

open Semigroup {{...}} public

-- Something to be a monoid has to be Semigroup.
-- State the identity rules.
record Monoid {i}{A : Set i}(_⊕_ : A → A → A)(e : A) : Set i where
  field
    overlap ⦃ semigroup ⦄ : {!!}
    idl : {x : A} → e ⊕ x ≡ x
    idr : {x : A} → x ⊕ e ≡ x

open Monoid {{...}} public

instance
-- Formalise the followings:
---- Natural numbers with _+_ form a semigroup
  ℕ+Semigroup : Semigroup _+_ 
  ℕ+Semigroup = record { assoc = λ {x y z} → assoc+ x y z } 

---- Natural numbers with _*_ form a semigroup
  ℕ*Semigroup : Semigroup _*_ 
  ℕ*Semigroup = record { assoc = λ {x y z} → assoc* x y z }

---- What can be the associative operation on lists?
  ListSemigroup : let open List in Semigroup _++_ 
  ListSemigroup = record { assoc = λ {x y z} →   List-assoc++  x y z }

-- The above ones also form a monoid.
  ℕ+Monoid : Monoid _+_ zero
  ℕ+Monoid = record { idl = refl ; idr =  λ {x} → idr+ x }


  ℕ*Monoid : Monoid _*_ (suc zero)
  ℕ*Monoid = record { idl = λ {x} → idr+ x ; idr = λ {x} → idr* x }

  ListMonoid : let open List in Monoid _++_ []
  ListMonoid = record { idl = refl ; idr = λ {x} → List-idr++ x }

-----------------------------
-- Real isomorphism
-----------------------------

-- We can define a type for actual isomorphism.
-- The ↔ type is just logical equivalence but it does not require us to be an isomorphism.
-- Isomorphism requires us to prove that the given two functions in ↔ composed in any order is the identity function.

-- \~= : ≅
infix 4 _≅_
record _≅_ {i j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  field
    equivalence : A ↔ B
    idₗ : ∀ a → snd equivalence (fst equivalence a) ≡ a -- funexted version
    idᵣ : ∀ b → fst equivalence (snd equivalence b) ≡ b

open _≅_ public

-- e.g.

Bool≅Fin2 : Bool ≅ Fin (suc (suc zero)) -- Fill in the above type holes in the instance block to be able to write the 2 literal here. (suc (suc zero) still works, just literals don't.)
fst (equivalence Bool≅Fin2) false = fzero
fst (equivalence Bool≅Fin2) true = fsuc fzero
snd (equivalence Bool≅Fin2) fzero = false
snd (equivalence Bool≅Fin2) (fsuc x) = true
idₗ Bool≅Fin2 false = refl
idₗ Bool≅Fin2 true = refl
idᵣ Bool≅Fin2 fzero = refl
idᵣ Bool≅Fin2 (fsuc fzero) = refl

-- Let's remember some of the equivalences from earlier excercise classes (2ⁿᵈ excersise class in particular).
{-
-- (⊎, ⊥) form a commutative monoid (kommutatív egységelemes félcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A

-- (×, ⊤) form a commutative monoid (kommutatív egységelemes félcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
idl× : {A : Set} → ⊤ × A ↔ A
idr× : {A : Set} → A × ⊤ ↔ A
null× : {A : Set} → A × ⊥ ↔ ⊥

-- distributivity of × and ⊎
dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)

-- exponentiation laws
curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
law^1 : {A : Set} → (⊤ → A) ↔ A
law1^ : {A : Set} → (A → ⊤) ↔ ⊤
-}

-- Choose one or two (or even all of them, these are not hard to prove) and try to formalise and then prove that going in either way we get back the original value.
-- To state it, you just need to change the ↔ with ≅
 