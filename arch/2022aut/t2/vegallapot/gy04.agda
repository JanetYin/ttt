open import lib

------------------------------------------------------
-- simple finite types
------------------------------------------------------

flip : ℕ × Bool → Bool × ℕ
flip (n , b) = b , n

flipback : Bool × ℕ → ℕ × Bool
flipback (b , n) = n , b

comm× : {A B : Set} → A × B → B × A
comm× (a , b) = b , a

comm×back : {A B : Set} → B × A → A × B
comm×back = comm×

--equality:  \equiv or \==
1issuczero : 1 ≡ suc zero
1issuczero = refl

1iszero : 1 ≡ zero
1iszero = {!!}      -- this will never have an element

b1 b2 : Bool × ⊤    --2 × 1 = 2 elements
b1 = true , tt
b2 = false , tt

--that's an interesting one:
--Agda can automatically deduce they're not equal
b1≠b2 : b1 ≡ b2 → ⊥    -- same as (b1 ≡ b2) → ⊥
b1≠b2 ()

t1 t2 : ⊤ ⊎ ⊤
t1 = inl tt
t2 = inr tt
t1≠t2 : t1 ≡ t2 → ⊥
t1≠t2 ()

bb1 bb2 bb3 : Bool ⊎ ⊤    -- 2 + 1 = 3
bb1 = inl false
bb2 = inl true
bb3 = inr tt
bb1≠bb2 : bb1 ≡ bb2 → ⊥
bb1≠bb2 ()
bb1≠bb3 : bb1 ≡ bb3 → ⊥
bb1≠bb3 ()
bb2≠bb3 : bb2 ≡ bb3 → ⊥
bb2≠bb3 ()

--which one exists?
ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)
ee = inr (λ x → tt)

ee2 : {A : Set} → (⊤ → ⊥) ⊎ (⊥ → A)
ee2 = inr exfalso

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)  --(1 + (1 * 0)) * (1 + 0)
d = inl tt , inl tt

sample : ((((⊤ × ⊤ × ⊥ × ⊤) ⊎ ⊤) ⊎ ⊥) ⊎ (⊥ × ⊤))
       × (((⊤ ⊎ (⊤ × ⊤)) ⊎ (⊤ × ⊤ × ⊤)) ⊎ (⊤ × ⊥ × ⊤))
sample = inl (inl (inr tt)) ,  inl (inl {!inr (tt , tt)!})

--what is an isomorphism?
--isomorphism between (Bool → A) functions and A × A constructs
from : {A : Set} → A × A → (Bool → A)
from (fst₁ , snd₁) = λ b → if b then fst₁ else snd₁
to : {A : Set} → (Bool → A) → A × A
to = λ f → f true , f false             --this is done for us
testfromto1 : {A : Set}{a b : A} → fst (to (from (a , b))) ≡ a
testfromto1 = refl
testfromto2 : {A : Set}{a b : A} → snd (to (from (a , b))) ≡ b
testfromto2 = refl
testfromto3 : {A : Set}{a b : A} → from (to (λ x → if x then a else b)) true ≡ a
testfromto3 = refl
testfromto4 : {A : Set}{a b : A} → from (to (λ x → if x then a else b)) false ≡ b
testfromto4 = refl

-- Curry–Howard?

------------------------------------------------------
-- all algebraic laws systematically
------------------------------------------------------

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C) -- isomorphism? or proof of a logical equivalence?
assoc⊎ = part1 , part2     -- C-u C-u C-c C-,
  where
  part1 : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  part1 (inl (inl x)) = inl x
  part1 (inl (inr x)) = inr (inl x)
  part1 (inr x) = inr (inr x)

  part2 : {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
  part2 (inl x) = inl (inl x)
  part2 (inr (inl x)) = inl (inr x)
  part2 (inr (inr x)) = inr x

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = (λ x → case x exfalso λ a → a) , λ a → inr a

--homework
idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = {!!}

--homework
comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = ((λ x → case x (λ a → inr a) λ b → inl b) , {!!})

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = (λ ((a , b) , c) → (a , b , c)) , λ (a , (b , c)) → (a , b) , c

{-
Statements we can use now:
⊤
3 ≡ 3  (an element of this is refl)
5 ≡ 5 (this has refl too)
-}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = ((λ (_ , a) → a) , λ a → (tt , a))

--homework
idr× : {A : Set} → A × ⊤ ↔ A
idr× = {!!}

-- ⊥ is a null element

--homework (hint: exfalso)
null× : {A : Set} → A × ⊥ ↔ ⊥
null× = {!!}

-- distributivity of × and ⊎

-- homework
dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = ((λ (a , buc) → case buc (λ b → inl ((a , b))) {!!}) , {!!})

-- exponentiation laws

curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C) -- also a proof!
curry = {!!}

⊎×→ : {A B C : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!!}

-- homework
law^0 : {A : Set} → (⊥ → A) ↔ ⊤   --logically, it would be enough to say (⊥ → A)
law^0 = {!!}

law^1 : {A : Set} → (⊤ → A) ↔ A
law^1 = {!!}

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = {!!}

--NOTE: homework until here

comm⊎' : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎' = (λ avb → case avb (λ a → inr a) λ b → inl b) , {!!}
---------------------------------------------------------
-- random isomorphisms
------------------------------------------------------

--homework
iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ A × B ⊎ (Bool → B)) -- Bool is not a proposition, so this is only an isomorphism
iso1 = (λ x → {!!}) , {!!}

--homework
iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))  -- a special case of an earlier one
iso2 = {!!}



iso3 : (⊤ ⊎ (⊤ ⊎ ⊤)) ↔ Bool ⊎ ⊤ -- now it must give different outputs to different inputs!
iso3 = part1 , part2
  where
  part1 : (⊤ ⊎ (⊤ ⊎ ⊤)) → Bool ⊎ ⊤
  part1 (inl tt) = inl true
  part1 (inr (inl tt)) = inl false
  part1 (inr (inr tt)) = inr tt
  part2 : Bool ⊎ ⊤ → (⊤ ⊎ (⊤ ⊎ ⊤))
  part2 (inl true) = inl tt
  part2 (inl false) = inr (inl tt)
  part2 (inr tt) = inr (inr tt)

--C-u C-u C-c C-,

testiso3 :  fst iso3 (inl tt) ≡ fst iso3 (inr (inl tt)) → ⊥ --same as ¬
testiso3 ()
testiso3' : fst iso3 (inl tt) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3'' ()
testiso3₂ : snd iso3 (inl true) ≡ snd iso3 (inl false) → ⊥
testiso3₂ ()
testiso3₂' : snd iso3 (inl true) ≡ snd iso3 (inr tt) → ⊥
testiso3₂' ()
testiso3₂'' : snd iso3 (inl false) ≡ snd iso3 (inr tt) → ⊥
testiso3₂'' ()


--homework
iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ (⊤ ⊎ ⊤) -- again mainly an isomorphism
iso4 = {!!} , {!!}
testiso4 : fst iso4 (λ _ → inl tt) ≡ fst iso4 (λ _ → inr (inr tt)) → ⊥
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≡ snd iso4 (inr tt) tt → ⊥
testiso4' ()
