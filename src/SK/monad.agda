module SK.monad where
    
open import Lib

record Monad (M : Set → Set) : Set₁ where

 constructor
  makeMonad

 field
  return : {X :  Set} → X → M X

  _>>=_  : {X Y :  Set} → M X → (X → M Y) → M Y

  requirement₀ : {X Y :  Set} (x : X) (f : X → M Y)
               → (return x >>= f) ≡ f x

  requirement₁ : {X :  Set} (m : M X)
               → (m >>= return) ≡ m

  requirement₂ : {X Y Z :  Set} (m : M _) (f : X → M Y) (g : Y → M Z)
               → ((m >>= f) >>= g) ≡ (m >>= (λ x → f x >>= g))


Maybe-Monad : Monad Maybe
Maybe-Monad = makeMonad return _>>=_ requirement₀ requirement₁ requirement₂
    where 
        return : {X : Set} → X → Maybe X 
        return = just
        _>>=_ : {X Y :  Set} → Maybe X → (X → Maybe Y) → Maybe Y
        just x >>= f = f x
        nothing >>= f = nothing
        requirement₀ : {X Y :  Set} (x : X) (f : X → Maybe Y) → (return x >>= f) ≡ f x
        requirement₀ x f = refl
        requirement₁ : {X :  Set} (m : Maybe X) → (m >>= return) ≡ m
        requirement₁ (just x) = refl
        requirement₁ nothing = refl 
        requirement₂ : {X Y Z :  Set} (m : Maybe _) (f : X → Maybe Y) (g : Y → Maybe Z) → ((m >>= f) >>= g) ≡ (m >>= (λ x → f x >>= g))
        requirement₂ (just x) f g = refl
        requirement₂ nothing f g = refl

List-idr++ : ∀{i}{A : Set i}(xs : List A) → let open List in xs ++ [] ≡ xs
List-idr++ {i} {A} [] = refl
List-idr++ {i} {A} (x ∷ xs) = cong (λ y → x ∷ y) (List-idr++ xs)

List-assoc++ : ∀{i}{A : Set i}(xs ys zs : List A) → let open List in (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
List-assoc++ {i} {A} [] ys zs = refl
List-assoc++ {i} {A} (x ∷ xs) ys zs = cong (x ∷_) (List-assoc++ {i} {A} xs ys zs)
 
 
List-Monad : Monad List
List-Monad = makeMonad return _>>=_ requirement₀ requirement₁ requirement₂
    where 
        return : {X : Set} → X → List X 
        return = λ x → x ∷ []
        _>>=_ : {X Y :  Set} → List X → (X → List Y) → List Y
        [] >>= f = []
        (x ∷ x₂) >>= f = (f x) List.++ (x₂ >>= f)
        requirement₀ : {X Y :  Set} (x : X) (f : X → List Y) → (return x >>= f) ≡ f x
        requirement₀ x f = List-idr++ (f x)
        requirement₁ : {X :  Set} (m : List X) → (m >>= return) ≡ m
        requirement₁ [] = refl
        requirement₁ (x ∷ m) = cong (x ∷_) (requirement₁ m)
        requirement₂ : {X Y Z :  Set} (m : List _) (f : X → List Y) (g : Y → List Z) → ((m >>= f) >>= g) ≡ (m >>= (λ x → f x >>= g))
        requirement₂ [] f g = refl 
        requirement₂ (x ∷ m) f g = {!   !} 
        -- with f x 
        -- ... | [] = requirement₂ m f g
        -- ... | x₁ ∷ y = {!   !}
        -- = (((f x List.++ []) >>= g))--((f x List.++ []) >>= g) ≡ (f x >>= g) List.++ []
        --                                                 ≡⟨ cong  (λ x → x >>= g) (List-idr++ (f x)) ⟩ 
        --                                       ((f x >>= g))
        --                                                 ≡⟨ sym (List-idr++ (f x >>= g)) ⟩ 
        --                                        refl
        -- requirement₂ (x ∷ x₁ ∷ m) f g = {!   !}
        -- with f x >>= g | f x 
        -- ... | [] | [] = {!   !}
        -- ... | [] | x₁ ∷ y = {!   !}
        -- ... | x₁ ∷ z | [] = {!   !}
        -- ... | x₁ ∷ z | x₂ ∷ y = {!   !}
        
        -- ... | [] = requirement₂ m f g
        -- ... | x₁ ∷ [] = {!   !}
        -- ... | x₁ ∷ x₂ ∷ y = {!   !}
        -- sym (trans ( (List-assoc++ (g x₁) (y >>= g) (m >>= (λ x₂ → f x₂ >>= g)) )) (cong (g x₁ List.++_) (sym {!  requirement₂  m f g !})))
           