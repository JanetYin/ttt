module libBool where
open import lib

eqb : Bool → Bool → Bool
eqb = λ a b → if a then b else not b

Eqb : Bool → Bool → Set
Eqb = λ a b → if eqb a b then ⊤ else ⊥

-- properties of Eqb

reflb : (b : Bool) → Eqb b b
reflb = indBool _ tt tt

transpb : (P : Bool → Set)(a b : Bool) → Eqb a b → P a → P b
transpb = λ P a → indBool 
  (λ a → (b : Bool) → Eqb a b → P a → P b)
  (λ b → indBool (λ b → Eqb true  b → P true  → P b) (λ _ w → w) exfalso     b)
  (λ b → indBool (λ b → Eqb false b → P false → P b) exfalso     (λ _ w → w) b)
  a

-- use transpb
symb : (a b : Bool) → Eqb a b → Eqb b a
symb a b e = transpb (λ b → Eqb b a) a b e (reflb a)

-- use transpb
transb : (a b c : Bool) → Eqb a b → Eqb b c → Eqb a c
transb a b c u v = transpb (λ c → Eqb a c) b c v u

-- every function on booleans is a congruence; use transpb to prove it
congb : (f : Bool → Bool) → (a b : Bool) → Eqb a b → Eqb (f a) (f b)
congb = λ f a b eq → transpb (λ x → Eqb (f a) (f x)) a b eq (reflb (f a))

-- disjointness of different constructors of Bool
disjb : ¬ Eqb true false
disjb = λ e → e

-- conjunction an disjunction

_∧_ : Bool → Bool → Bool
_∧_ = λ x y → if x then y else false
infixl 7 _∧_

_∨_ : Bool → Bool → Bool
_∨_ = λ x y → if x then true else y
infixl 5 _∨_

-- properties of _∧_ and _∨_

idl∧ : (a : Bool) → Eqb (true ∧ a)  a
idl∧ = indBool (λ b → Eqb (true ∧ b) b) tt tt

idr∧ : (a : Bool) → Eqb (a ∧ true)  a
idr∧ = indBool (λ b → Eqb (b ∧ true) b) tt tt

ass∧ : (a b c : Bool) → Eqb ((a ∧ b) ∧ c) (a ∧ (b ∧ c))
ass∧ = λ a b c → indBool (λ a → Eqb ((a ∧ b) ∧ c) (a ∧ (b ∧ c)))
                         (reflb (b ∧ c))
                         (reflb false)
                         a

comm∧ : (a b : Bool) → Eqb (a ∧ b) (b ∧ a)
comm∧ = λ a b → indBool (λ a → Eqb (a ∧ b) (b ∧ a))
                        (transb (true ∧ b) b (b ∧ true) (idl∧ b) (symb (b ∧ true) b (idr∧ b)))
                        ((transb (false ∧ b) false (b ∧ false) (reflb false) (indBool (λ b → Eqb false (b ∧ false)) tt tt b)))
                        a

null∧ : (a : Bool) → Eqb (false ∧ a) false
null∧ = λ _ → reflb false

idl∨ : (a : Bool) → Eqb (false ∨ a) a
idl∨ = reflb

idr∨ : (a : Bool) → Eqb (a ∨ false) a
idr∨ = indBool (λ a → Eqb (a ∨ false) a) tt tt

ass∨ : (a b c : Bool) → Eqb ((a ∨ b) ∨ c) (a ∨ (b ∨ c))
ass∨ = λ a b c → indBool (λ a → Eqb ((a ∨ b) ∨ c) (a ∨ (b ∨ c)))
                         (reflb true)
                         (reflb (b ∨ c))
                         a

comm∨ : (a b : Bool) → Eqb (a ∨ b) (b ∨ a)
comm∨ = indBool (λ a → (b : Bool) → Eqb (a ∨ b) (b ∨ a))
                          (indBool (λ b → Eqb (true ∨ b) (b ∨ true)) tt tt)
                          (indBool (λ b → Eqb (false ∨ b) (b ∨ false)) tt tt)

null∨ : (a : Bool) → Eqb (true ∨ a) true
null∨ = λ _ → reflb true

dist∧ : (a b c : Bool) → Eqb (a ∧ (b ∨ c)) (a ∧ b ∨ a ∧ c)
dist∧ = indBool (λ a → (b c : Bool) → Eqb (a ∧ (b ∨ c)) (a ∧ b ∨ a ∧ c))
                          (indBool (λ b → (c : Bool) → Eqb (true ∧ (b ∨ c)) (true ∧ b ∨ true ∧ c)) 
                                   (indBool (λ c → Eqb (true ∧ (true ∨ c)) (true ∧ true ∨ true ∧ c)) tt tt)
                                   (indBool (λ c → Eqb (true ∧ (false ∨ c)) (true ∧ false ∨ true ∧ c)) tt tt)
                          )
                          (indBool (λ b → (c : Bool) → Eqb (false ∧ (b ∨ c)) (false ∧ b ∨ false ∧ c)) 
                                   (indBool (λ c → Eqb (false ∧ (true ∨ c)) (false ∧ true ∨ false ∧ c)) tt tt)
                                   (indBool (λ c → Eqb (false ∧ (false ∨ c)) (false ∧ false ∨ false ∧ c)) tt tt)
                          )

dist∨ : (a b c : Bool) → Eqb (a ∨ (b ∧ c)) ((a ∨ b) ∧ (a ∨ c))
dist∨ = indBool (λ a → (b c : Bool) → Eqb (a ∨ (b ∧ c)) ((a ∨ b) ∧ (a ∨ c)))
                          (indBool (λ b → (c : Bool) → Eqb (true ∨ (b ∧ c)) ((true ∨ b) ∧ (true ∨ c))) 
                                   (indBool (λ c → Eqb (true ∨ (true ∧ c)) ((true ∨ true) ∧ (true ∨ c))) tt tt)
                                   (indBool (λ c → Eqb (true ∨ (false ∧ c)) ((true ∨ false) ∧ (true ∨ c))) tt tt)
                          )
                          (indBool (λ b → (c : Bool) → Eqb (false ∨ (b ∧ c)) ((false ∨ b) ∧ (false ∨ c))) 
                                   (indBool (λ c → Eqb (false ∨ (true ∧ c)) ((false ∨ true) ∧ (false ∨ c))) tt tt)
                                   (indBool (λ c → Eqb (false ∨ (false ∧ c)) ((false ∨ false) ∧ (false ∨ c))) tt tt)
                          )

abs∧ : (a b : Bool) → Eqb (a ∧ (a ∨ b)) a
abs∧ = λ a b → indBool (λ a → Eqb (a ∧ (a ∨ b)) a) tt tt a

abs∨ : (a b : Bool) → Eqb (a ∨ (a ∧ b)) a
abs∨ = λ a b → indBool (λ a → Eqb (a ∨ (a ∧ b)) a) tt tt a
