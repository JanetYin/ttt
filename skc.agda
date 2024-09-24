open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)
open import Data.Product using (_×_; Σ  ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import plfa.part2.Substitution using (Rename; Subst)
open import plfa.part2.Untyped 
  using ( β; ζ;
  abs-cong; 
  _⊢_;  `_; #_; _,_; ★; ƛ_;  _[_];
  rename; ext; exts;  subst; subst-zero)
-- postulate String : Set
-- {-# BUILTIN STRING String #-}
infix 2 _⇛ₛ_



--     ⟦_⟧ : Syn.Tm → Tm
--     ⟦·⟧ : ∀{t u} →  ⟦ t Syn.· u ⟧ ≡  ⟦ t ⟧ ·  ⟦ u ⟧
--     ⟦K⟧ : ⟦ Syn.K ⟧ ≡ K
--     ⟦S⟧ : ⟦ Syn.S ⟧ ≡ S
--   {-# REWRITE ⟦·⟧ ⟦K⟧ ⟦S⟧ #-}


infixl 5 _·_ 
data Term : Set where
  K   :  Term
  Sₛ   :  Term
  _·_ :  Term → Term → Term


data _⇛ₛ_ : Term → Term → Set where
  -- K₀ : K ⇛ₛ K
  -- S₀ : Sₛ ⇛ₛ Sₛ
  T₀  : ∀{x} → x ⇛ₛ x
  -- -- T₀ : 
  pk   : ∀{x y }   → K · x · y ⇛ₛ x
  ps   : ∀{x y z }  → Sₛ · x · y · z ⇛ₛ (x · z) · (y · z) -- x ⇛ₛ x' → y ⇛ₛ y' → z ⇛ₛ z'
  papp : ∀{L L' M M'} → L ⇛ₛ L' → M ⇛ₛ M' → L · M ⇛ₛ L' · M' 

data NF : Set where
  K₀ : NF
  K₁ : NF → NF
  S₀ : NF
  S₁ : NF → NF
  S₂ : NF → NF → NF

-- data RTm : Set where 
--   Kᵣ : RTm 
--   Sᵣ : RTm 
--   _·ᵣ_ : RTm  → RTm → RTm 
-- postulate 
--     Tm : Set 
--     η : RTm → Set 
--     eq : (t₀ t₁ u : RTm) → {! t₀ ⇛* u → ?  !} 
--     iteTm : (A : Set)(f : RTm → A) (e : ∀{t₀ t₁ u} → {!   !} → {!   !} → {!   !})  → RTm → A 
    

-- par-refl : ∀{M : Term} → M ⇛ₛ M
-- par-refl {K} = T₀
-- par-refl {Sₛ} = T₀
-- par-refl {M · M₁} = papp par-refl par-refl

-- par-triangle' : ∀ {M N N' : Term}
--   → M ⇛ₛ N
--     -------
--   → N ⇛ₛ N'
-- par-triangle' {M} {N} {N'} x = {!   !}
diamond-single₁ : ∀{t t₀ t₁  : Term} → t ⇛ₛ t₀ → t ⇛ₛ t₁ →  Σ Term  (λ t' → (t₀ ⇛ₛ t') × (t₁ ⇛ₛ t'))
diamond-single₁ = {!   !}

diamond-single : ∀{t t₀ t₁  : Term} → t ⇛ₛ t₀ → t ⇛ₛ t₁ →  Σ Term  (λ t' → (t₀ ⇛ₛ t') × (t₁ ⇛ₛ t'))
diamond-single {t} {.t} {.t} T₀ T₀ = ⟨ t , ⟨ T₀ , T₀ ⟩ ⟩
diamond-single {.(K · t₁ · _)} {.(K · t₁ · _)} {t₁} T₀ pk = ⟨ t₁ , ⟨ pk , T₀ ⟩ ⟩
diamond-single {(Sₛ · x · y · z)} {(Sₛ · x · y · z)} {(x · z · (y · z))} T₀ ps = ⟨ x · z · (y · z) , ⟨ ps , T₀ ⟩ ⟩
diamond-single {(L · M)} {(L · M)} {(L' · M')} T₀ (papp x₁ x₂) = ⟨ (L' · M') , ⟨ (papp x₁ x₂) , T₀ ⟩ ⟩
diamond-single {.(K · t₀ · _)} {t₀} {.(K · t₀ · _)} pk T₀ = ⟨ t₀ , ⟨ T₀ , pk ⟩ ⟩
diamond-single {.(K · t₀ · _)} {t₀} {.t₀} pk pk = ⟨ t₀ ,  ⟨ T₀ , T₀ ⟩  ⟩
diamond-single {K · t₀ · y} {t₀} {.(K · t₀) · .y} pk (papp T₀ T₀) = ⟨ t₀ , ⟨ T₀ , pk ⟩ ⟩
diamond-single {K · t₀ · .(K · M · _)} {t₀} {.(K · t₀) · M} pk (papp T₀ pk) = ⟨ t₀ , ⟨ T₀ , pk ⟩ ⟩
diamond-single {K · t₀ · .(Sₛ · _ · _ · _)} {t₀} {.(K · t₀) · .(_ · _ · (_ · _))} pk (papp T₀ ps) = ⟨ t₀ , ⟨ T₀ , pk ⟩ ⟩
diamond-single {K · t₀ · .(_ · _)} {t₀} {.(K · t₀) · .(_ · _)} pk (papp T₀ (papp x₂ x₃)) = ⟨ t₀ , ⟨ T₀ , pk ⟩ ⟩
diamond-single {K · t₀ · y} {t₀} {(K · M') · .y} pk (papp (papp T₀ x₂) T₀) = ⟨ M' , ⟨ x₂ , pk ⟩ ⟩ --⟨ {!   !} , {!   !} ⟩
diamond-single {K · t₀ · .(K · M · _)} {t₀} {(K · M') · M} pk (papp (papp T₀ x₂) pk) = ⟨ M' , ⟨ x₂ , pk ⟩ ⟩
diamond-single {K · t₀ · .(Sₛ · _ · _ · _)} {t₀} {(K · M') · .(_ · _ · (_ · _))} pk (papp (papp T₀ x₂) ps) = ⟨ M' , ⟨ x₂ , pk ⟩ ⟩
diamond-single {K · t₀ · .(_ · _)} {t₀} {(K · M') · .(_ · _)} pk (papp (papp T₀ x₂) (papp x₃ x₄)) = ⟨ M' , ⟨ x₂ , pk ⟩ ⟩ 
diamond-single {(Sₛ · x · y · z)} {.(x · z · (y · z))} {.(Sₛ · x · y · z)} ps T₀ = ⟨ x · z · (y · z) , ⟨ T₀ , ps ⟩ ⟩
diamond-single {(Sₛ · x · y · z)} {.(x · z · (y · z))} {.(x · z · (y · z))} ps ps = ⟨ x · z · (y · z) , ⟨ T₀ , T₀ ⟩ ⟩
diamond-single {Sₛ · x · y · z} {.(x · z · (y · z))} {.(Sₛ · x · y) · .z} ps (papp T₀ T₀) = ⟨ (x · z · (y · z)) , ⟨ T₀ , ps ⟩ ⟩
diamond-single {Sₛ · x · y · (K · M' · M'')} {.(x · (K · M' · M'') · (y · (K · M' · M'')))} {.(Sₛ · x · y) · M'} ps (papp T₀ pk) = ⟨ (x ·  M'  · (y · M' )) , ⟨ papp (papp (T₀ {x}) (pk {M'} {M''})) (papp (T₀ {y}) (pk {M'} {M''})) , ps ⟩ ⟩
diamond-single {Sₛ · x · y · (Sₛ · f · g · u)} {.(x · (Sₛ · f · g · u) · (y · (Sₛ · f · g · u)))} {.(Sₛ · x · y) · .(f · u · (g · u))} ps (papp T₀ ps) = ⟨ (x · (f · u · (g · u)) · (y · (f · u · (g · u)))) , ⟨ papp (papp (T₀ {x}) (ps {f} {g} {u}) ) (papp (T₀ {y}) (ps {f} {g} {u})) , ps ⟩ ⟩ 
diamond-single {Sₛ · x · y · (L · M)} {.(x · (L · M) · (y · (L · M)))} {.(Sₛ · x · y) · (L' · M')} ps (papp T₀ (papp x₂ x₃)) =  ⟨ (x · (L' · M') · (y · (L' · M')) ) , ⟨ (papp (papp  (T₀ {x}) (papp x₂ x₃) ) (papp  (T₀ {y}) (papp x₂ x₃) )) , ps ⟩ ⟩ 
diamond-single {Sₛ · x · y · z} {.(x · z · (y · z))} {.(Sₛ · x · y) · .z} ps (papp (papp T₀ T₀) T₀) = ⟨ (x · z · (y · z)) , ⟨ T₀ , ps ⟩ ⟩
diamond-single {Sₛ · x · y · z} {.(x · z · (y · z))} {Sₛ · .x · y · .z} ps (papp (papp (papp T₀ T₀) T₀) T₀) = ⟨ (x · z · (y · z)) , ⟨ T₀ , ps ⟩ ⟩
diamond-single {Sₛ · .(K · x' · _) · y · z} {.(K · x' · _ · z · (y · z))} {Sₛ · x' · y · .z} ps (papp (papp (papp T₀ pk) T₀) T₀) = ⟨ (x' · z · (y · z)) , ⟨ (papp  (papp pk (T₀ {z }))  (T₀ {(y · z) })) , ps ⟩ ⟩
diamond-single {Sₛ · .(Sₛ · _ · _ · _) · y · z} {.(Sₛ · _ · _ · _ · z · (y · z))} {Sₛ · .(_ · _ · (_ · _)) · y · .z} ps (papp (papp (papp T₀ ps) T₀) T₀) = ⟨ (_ · _ · (_ · _) · z ) · (y · z) , ⟨ papp (papp ps  (T₀ {z }))(T₀ {y · z}) , ps ⟩ ⟩
diamond-single {Sₛ · .(_ · _) · y · z} {.(_ · _ · z · (y · z))} {Sₛ · .(_ · _) · y · .z} ps (papp (papp (papp T₀ (papp x₂ x₃)) T₀) T₀) = ⟨ (_ · _ · z · (y · z)) , ⟨ papp (papp   (papp x₂ x₃) (T₀ {z }))(T₀ {(y · z) }) , ps ⟩ ⟩ 
diamond-single {Sₛ · x · .(K · _ · _) · z} {.(x · z · (K · _ · _ · z))} {.(Sₛ · x · _) · .z} ps (papp (papp T₀ pk) T₀) = ⟨ x · z · (_ · z) , ⟨ (papp (T₀ {x · z}) (papp pk (T₀ {z}))) , ps ⟩ ⟩
diamond-single {Sₛ · x · .(K · _ · _) · z} {.(x · z · (K · _ · _ · z))} {.(Sₛ · _ · _) · .z} ps (papp (papp (papp T₀ x₂) pk) T₀) = ⟨ _ · z · (_ · z) , ⟨ (papp  (papp x₂ (T₀ {z})) (papp pk (T₀ {z}))) , ps ⟩ ⟩ --⟨ {!   !} , {!   !} ⟩
diamond-single {Sₛ · x · .(Sₛ · _ · _ · _) · z} {.(x · z · (Sₛ · _ · _ · _ · z))} {.(Sₛ · x · (_ · _ · (_ · _))) · .z} ps (papp (papp T₀ ps) T₀) = ⟨ (x · z · (_ · _ · (_ · _) · z)) , ⟨ papp (T₀ {x · z}) (papp ps (T₀ {z}) ) , ps ⟩ ⟩
diamond-single {Sₛ · x · .(Sₛ · _ · _ · _) · z} {.(x · z · (Sₛ · _ · _ · _ · z))} {.(Sₛ · _ · (_ · _ · (_ · _))) · .z} ps (papp (papp (papp T₀ x₂) ps) T₀) = ⟨ _ · z · (_ · _ · (_ · _) · z) , ⟨ (papp   (papp x₂ (T₀ {z}))  (papp ps (T₀ {z}))) , ps ⟩ ⟩
diamond-single {Sₛ · x · .(_ · _) · z} {.(x · z · (_ · _ · z))} {.(Sₛ · x · (_ · _)) · .z} ps (papp (papp T₀ (papp x₂ x₃)) T₀) = ⟨ (x · z · (_ · _ · z)) , ⟨ (papp (T₀ {x · z}) (papp (papp x₂ x₃) (T₀ {z}))) , ps ⟩ ⟩
diamond-single {Sₛ · x · .(_ · _) · z} {.(x · z · (_ · _ · z))} {.(Sₛ · _ · (_ · _)) · .z} ps (papp (papp (papp T₀ x₄) (papp x₂ x₃)) T₀) = ⟨ (_ · z · (_ · _ · z)) , ⟨ (papp  (papp x₄ (T₀ {z})) (papp (papp x₂ x₃) (T₀ {z}))) , ps ⟩ ⟩ 
diamond-single {Sₛ · x · y · .(K · M' · _)} {.(x · (K · M' · _) · (y · (K · M' · _)))} {.(Sₛ · x · _) · M'} ps (papp (papp T₀ x₂) pk) = ⟨ x · _ · (_ · _) , ⟨ papp (papp (T₀ {x}) pk) (papp x₂ pk) , ps ⟩ ⟩
diamond-single {Sₛ · x · y · .(K · M' · _)} {.(x · (K · M' · _) · (y · (K · M' · _)))} {.(Sₛ · _ · _) · M'} ps (papp (papp (papp T₀ x₃) x₂) pk) = ⟨ _ · _ · (_ · _) , ⟨ papp (papp x₃ pk) (papp x₂ pk) , ps ⟩ ⟩
diamond-single {Sₛ · x · y · .(Sₛ · _ · _ · _)} {.(x · (Sₛ · _ · _ · _) · (y · (Sₛ · _ · _ · _)))} {.(Sₛ · x · _) · .(_ · _ · (_ · _))} ps (papp (papp T₀ x₂) ps) = ⟨ _ · (_ · _ · (_ · _)) · (_ · (_ · _ · (_ · _))) , ⟨ (papp (papp (T₀ {x}) ps) (papp x₂ ps)) , ps ⟩ ⟩
diamond-single {Sₛ · x · y · .(Sₛ · _ · _ · _)} {.(x · (Sₛ · _ · _ · _) · (y · (Sₛ · _ · _ · _)))} {.(Sₛ · _ · _) · .(_ · _ · (_ · _))} ps (papp (papp (papp T₀ x₃) x₂) ps) = ⟨ _ · (_ · _ · (_ · _)) · (_ · (_ · _ · (_ · _))) , ⟨ (papp (papp x₃ ps) (papp x₂ ps)) , ps ⟩ ⟩ --⟨ {!   !} , {!   !} ⟩
diamond-single {Sₛ · x · y · .(_ · _)} {.(x · (_ · _) · (y · (_ · _)))} {.(Sₛ · x · _) · .(_ · _)} ps (papp (papp T₀ x₂) (papp x₃ x₄)) = ⟨ (_ · (_ · _) · (_ · (_ · _))) , ⟨ (papp (papp (T₀ {x}) (papp x₃ x₄)) ( papp x₂ (papp x₃ x₄))) , ps ⟩ ⟩
diamond-single {Sₛ · x · y · .(_ · _)} {.(x · (_ · _) · (y · (_ · _)))} {.(Sₛ · _ · _) · .(_ · _)} ps (papp (papp (papp T₀ x₅) x₂) (papp x₃ x₄)) = ⟨ (_ · (_ · _) · (_ · (_ · _))) , ⟨ ((papp (papp x₅ (papp x₃ x₄)) ( papp x₂ (papp x₃ x₄)))) , ps ⟩ ⟩ 
diamond-single {(L · M)} {(L' · M')} {(L · M)} (papp x x₁) T₀ = ⟨ L' · M' , ⟨ T₀ , (papp x x₁) ⟩ ⟩
diamond-single {.(K · t₁ · _)} {.(K · t₁) · M'} {t₁} (papp T₀ x₁) pk = ⟨ t₁ , ⟨ pk , T₀ ⟩ ⟩
diamond-single {.(K · t₁ · _)} {.(K · _) · M'} {t₁} (papp (papp T₀ x₂) x₁) pk = ⟨ _ , ⟨ pk , x₂ ⟩ ⟩ 
diamond-single {Sₛ · f · g · u} {.(Sₛ · f · g) · M'} {.(f · u · (g · u))} (papp T₀ x₁) ps = ⟨ (f · _ · (_ · _)) , ⟨ ps , papp (papp (T₀ {f}) x₁) (papp (T₀ {g}) x₁) ⟩ ⟩
diamond-single {Sₛ · f · g · u} {.(Sₛ · f · _) · M'} {.(f · u · (g · u))} (papp (papp T₀ x₂) x₁) ps = ⟨ (f · _ · (_ · _)) , ⟨ ps , (papp (papp (T₀ {f}) x₁) (papp x₂ x₁)) ⟩ ⟩
diamond-single {Sₛ · f · g · u} {.(Sₛ · _ · _) · M'} {.(f · u · (g · u))} (papp (papp (papp T₀ x₃) x₂) x₁) ps = ⟨ (_ · _ · (_ · _)) , ⟨ ps , (papp (papp x₃ x₁) (papp x₂ x₁)) ⟩ ⟩ --⟨ {!   !} , {!   !} ⟩ --⟨ L' · M' , ⟨ T₀ , Trans_tri ps (papp x x₁) ⟩ ⟩
diamond-single {(L' · M')} {(L · M)} {(L'' · M'')} (papp x x₁) (papp x₂ x₃) = ⟨ ((proj₁ (diamond-single x x₂)) · (proj₁ (diamond-single x₁ x₃))) , ⟨ (papp (proj₁ (proj₂ (diamond-single x x₂))) (proj₁ (proj₂ (diamond-single x₁ x₃)) )) , (papp (proj₂ (proj₂ (diamond-single x x₂))) (proj₂ (proj₂ (diamond-single x₁ x₃)) )) ⟩ ⟩ 

{-(proj₁ (diamond-single x x₂)) · (proj₁ (diamond-single x₁ x₃))
(proj₂ (diamond-single x x₂))  (proj₂ (diamond-single x₁ x₃))
proj₁ (proj₂ (diamond-single x x₂)) L ⇛ₛ proj₁ (diamond-single x x₂)
proj₂ (proj₂ (diamond-single x x₂)) L'' ⇛ₛ proj₁ (diamond-single x x₂)
proj₁ (proj₂ (diamond-single x₁ x₃))  M ⇛ₛ proj₁ (diamond-single x₁ x₃)
proj₂ (proj₂ (diamond-single x₁ x₃))  M'' ⇛ₛ proj₁ (diamond-single x₁ x₃)
-}
infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _∎
data _⇛*_ :  Term → Term → Set where

  _∎ : ∀ {M : Term} → M ⇛* M

  _⇛⟨_⟩_ : ∀ {L M N : Term}
    → L ⇛ₛ M
    → M ⇛* N
      ---------
    → L ⇛* N

-- _⁺ :  Term → Term
-- K ⁺ = K
-- Sₛ ⁺ = Sₛ
-- (L · M) ⁺ = L ⁺ · (M ⁺)  

-- par-diamond : ∀{M N N' : Term} → M ⇛ₛ N → M ⇛ₛ N' → Σ[ L ∈ Term ] (N ⇛ₛ L) × (N' ⇛ₛ L)
-- par-diamond {M = M}  x x₁ = ⟨ (M ⁺) , ⟨ (par-triangle x) , (par-triangle x₁) ⟩ ⟩

  
strip : ∀{M N N′ : Term}
  → M ⇛ₛ N
  → M ⇛* N′
    ------------------------------------
  → Σ[ L ∈ Term ] (N ⇛* L)  ×  (N′ ⇛ₛ L)
strip {L} {M} {.L} LM _∎ = ⟨ M , ⟨ _∎ , LM ⟩ ⟩
strip {L} {M} {N} L₁M (_⇛⟨_⟩_ L⇛ₛM₁ L⇛*N) with strip (proj₁ (proj₂ (diamond-single L⇛ₛM₁ L₁M))) L⇛*N 
... | ⟨ L , ⟨ fst⇛*L , N⇛ₛL ⟩ ⟩ = ⟨ L , ⟨ (_⇛⟨_⟩_ (proj₂ (proj₂ (diamond-single L⇛ₛM₁ L₁M))) fst⇛*L) , N⇛ₛL ⟩ ⟩ 

-- diamond-multi : ∀{t t₀ t₁  : Term} →  t ⇛* t₀ → t ⇛* t₁ → Σ[ t' ∈ Term ] (t₀ ⇛* t') × (t₁ ⇛* t')
-- diamond-multi {t} {.t} {.t} _∎ _∎ = ⟨ t , ⟨ _∎ , _∎ ⟩ ⟩
-- diamond-multi {t} {.t} {t₁} _∎ (_⇛⟨_⟩_ tm mt₁) = ⟨ t₁ , ⟨ (_⇛⟨_⟩_  tm mt₁) , _∎ ⟩  ⟩
-- diamond-multi {t} {t₀} {.t} (_⇛⟨_⟩_ t⇛ₛM M⇛*t₀) _∎ = ⟨ t₀ , ⟨ _∎ , (_⇛⟨_⟩_ t⇛ₛM M⇛*t₀) ⟩ ⟩
-- diamond-multi {t} {t₀} {t₁} (_⇛⟨_⟩_ t⇛ₛM M⇛*t₀) (_⇛⟨_⟩_ t⇛ₛM₁ M₁⇛*t₁) with diamond-single t⇛ₛM t⇛ₛM₁
-- ... | ⟨ T , ⟨  M⇛ₛT , M₁⇛ₛT ⟩ ⟩ = {!   !} -- with par-confluence M⇛*t₀ M₁⇛*t₁ = {!   !}

par-confluence : ∀{L M₁ M₂ : Term}
  → L ⇛* M₁
  → L ⇛* M₂
    ------------------------------------
  → Σ[ N ∈ Term ] (M₁ ⇛* N) × (M₂ ⇛* N)
par-confluence {L} {.L} {.L} _∎ _∎ = ⟨ L , ⟨ _∎ , _∎ ⟩ ⟩
par-confluence {L} {.L} {N} _∎ (_⇛⟨_⟩_ lm mn) = ⟨ N , ⟨ (_⇛⟨_⟩_  lm mn) , _∎ ⟩ ⟩
par-confluence {L} {M₁} {.L} (_⇛⟨_⟩_ L⇛ₛM M⇛*M₁) _∎ = ⟨ M₁ , ⟨ _∎ , (_⇛⟨_⟩_ L⇛ₛM M⇛*M₁) ⟩ ⟩
par-confluence {L} {M₁} {M₂} (_⇛⟨_⟩_ L⇛ₛM M⇛*M₁) (_⇛⟨_⟩_ L⇛ₛM₃ L⇛*M₂) with strip L⇛ₛM (_⇛⟨_⟩_  L⇛ₛM₃ L⇛*M₂) 
... | ⟨ R , ⟨ M⇛*R , M₂⇛ₛR ⟩ ⟩ with par-confluence M⇛*M₁ M⇛*R 
... | ⟨ N' , ⟨ M₁⇛*N' , R⇛*N' ⟩ ⟩ = ⟨ N' , ⟨ M₁⇛*N' , _⇛⟨_⟩_ M₂⇛ₛR R⇛*N' ⟩ ⟩ 


multi-t·u : ∀ {t u t' u' : Term} → t ⇛* t' → u  ⇛* u' → t · u  ⇛*  t' · u' 
multi-t·u {t} {u} {.t} {.u} _∎ _∎ = _∎ {t · u}
multi-t·u {t} {u} {.t} {u'} _∎ (_⇛⟨_⟩_ x x₁) = _⇛⟨_⟩_  (papp (T₀ {t} ) x )  (multi-t·u  _∎ x₁)
multi-t·u {t} {u} {t'} {.u} (_⇛⟨_⟩_ x x₁) _∎ = _⇛⟨_⟩_  (papp x (T₀ {u}))  (multi-t·u  x₁ _∎)
multi-t·u {t} {u} {t'} {u'} (_⇛⟨_⟩_ x x₁) (_⇛⟨_⟩_ x₂ x₃) = _⇛⟨_⟩_ (papp x x₂) (multi-t·u  x₁ x₃)


data RTm : Set where 
  Kᵣ : RTm 
  Sᵣ : RTm 
  _·ᵣ_ : RTm  → RTm → RTm 
-- postulate 
--     Tm : Set 
--     η : RTm → Set 
--     eq : (t₀ t₁ u : RTm) → {! t₀ ⇛* u → ?  !} 
--     iteTm : (A : Set)(f : RTm → A) (e : ∀{t₀ t₁ u} → {!   !} → {!   !} → {!   !})  → RTm → A 
   
record Model : Set₁ where
  infixl 5 _·ₘ_
  field
    Tm  : Set
    _·ₘ_ : Tm → Tm → Tm
    Kₘ Sₘ : Tm
    Kβ  : ∀{u f} → Kₘ ·ₘ u ·ₘ f ≡ u
    Sβ  : ∀{f g u} → Sₘ ·ₘ f ·ₘ g ·ₘ u ≡ f ·ₘ u ·ₘ (g ·ₘ u)
  -- postulate
open Model 
module pInfiniteCombinators (m : Model) where
  open Model m
  
  
module InfiniteModel
  -- (Tm : RTm)
  (_·ₘ_  :  RTm → RTm → RTm)
  -- (let infixl 5 _·_; _·_ = _·_)
  (Kₘ Sₘ :  RTm)
  (Kβ : {u f : RTm} → (Kₘ ·ₘ u) ·ₘ f ≡ u)
  (Sβ :  {f g u : RTm} → ((Sₘ ·ₘ f) ·ₘ g) ·ₘ u ≡ (f ·ₘ u) ·ₘ (g ·ₘ u))

  where

{-Eqv
-- data _—→_ : Term → Term → Set where
--   β-K : ∀{x y} → (K · x · y) —→ x
--   β-Sₛ : ∀{x y z} → (Sₛ · x  · y · z) —→ ((x · z) · (y · z))
--   ξ₁ : ∀{L L' M} → L —→ L' → (L · M) —→ ((L' · M))
--   ξ₂ : ∀{L M M'} → M —→ M' → ((L · M)) —→ (L · M')

-- infix  2 _—↠_
-- infix  1 begin_
-- infixr 2 _—→⟨_⟩_
-- -- infix  3 _∎

-- data _—↠_ : Term → Term → Set where

--   _∎ : (M : Term)
--       ------
--     → M —↠ M

--   step—→ :  {M N L : Term}
--     → M —↠ N
--     → L —→ M
--       ------
--     → L —↠ N

-- pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

-- begin_ : ∀ {M N : Term}
--   → M —↠ N
--     ------
--   → M —↠ N
-- begin M—↠N = M—↠N

-- reduction-par : ∀{M N : Term} → M —→ N → M ⇛ₛ N
-- reduction-par {.(K · N · _)} {N} β-K = pk (par-refl {N})
-- reduction-par {Sₛ · x · y · z} {x · z · (y · z)} β-Sₛ = ps (par-refl {x}) (par-refl {y}) (par-refl {z})
-- reduction-par {M · M₁} {N · .M₁} (ξ₁ x) = papp (reduction-par {M} {N} x) (par-refl {M₁})
-- reduction-par {M · M₁} {.M · N₁} (ξ₂ x) = papp (par-refl {M}) (reduction-par {M₁} {N₁} x)

-- betas-pars : ∀{M N : Term}
--   → M —↠ N
--     ------
--   → M ⇛* N
-- betas-pars {K} {.K} (.K ∎) = _∎ {K} 
-- betas-pars {Sₛ} {.Sₛ} (.Sₛ ∎) = _∎ {Sₛ}
-- betas-pars {M · M₁} {.(M · M₁)} (.(M · M₁) ∎) = _∎ {M · M₁} 
-- betas-pars {M · M₁} {N} (step—→ b bs) = _⇛⟨_⟩_ (reduction-par bs) (betas-pars b)  

-- —↠-trans : ∀{L M N : Term}
--          → L —↠ M
--          → M —↠ N
--          → L —↠ N
-- —↠-trans {L} {.L} {N} (.L ∎) x₁ = x₁
-- —↠-trans {L} {M} {N} (step—→ mm lm) mn = step—→ (—↠-trans mm mn) lm


-- infixr 2 _—↠⟨_⟩_

-- _—↠⟨_⟩_ : ∀  {L M N : Term}
--     → L —↠ M
--     → M —↠ N
--       ---------
--     → L —↠ N
-- _—↠⟨_⟩_ lm mn = —↠-trans lm mn

-- appL-cong : ∀ {L L' M : Term}
--          → L —↠ L'
--            ---------------
--          → L · M —↠ L' · M
-- appL-cong {L} {.L} {M} (.L ∎) = L · M  ∎
-- appL-cong {L} {L'} {M} (step—→ x x₁) = step—→ (appL-cong x) (ξ₁ x₁)

-- appR-cong : ∀  {L M M' : Term}
--          → M —↠ M'
--            ---------------
--          → L · M —↠ L · M'
-- appR-cong {L} {M} {.M} (.M ∎) = L · M  ∎
-- appR-cong {L} {M} {M'} (step—→ x x₁) = step—→ (appR-cong x) (ξ₂ x₁)

-- par-betas : ∀{M N : Term}
--   → M ⇛ₛ N
--     ------
--   → M —↠ N
-- par-betas {.K} {.K} K₀ = K ∎
-- par-betas {.Sₛ} {.Sₛ} S₀ = Sₛ ∎
-- par-betas {.(K · _ · _)} {N} (pk x) = step—→ (par-betas x) β-K
-- par-betas {Sₛ · f · g · u} {(f' · u' · (g' · u'))} (ps x x₁ x₂) = step—→ 
--                                                                           (—↠-trans (appR-cong {f · u} (—↠-trans (appL-cong (par-betas x₁)) (appR-cong (par-betas x₂)))) (appL-cong {f · u} {f' · u'} {(g' · u')} 
--                                                                           ((—↠-trans (appL-cong (par-betas x)) (appR-cong (par-betas x₂)))))) β-Sₛ
-- par-betas {.(_ · _)} {.(_ · _)} (papp x x₁) = —↠-trans ( appL-cong (par-betas x)) (appR-cong (par-betas x₁))

-- pars-betas : ∀{M N : Term}
--   → M ⇛* N
--     ------
--   → M —↠ N
-- pars-betas {M} {.M} _∎ = M ∎ 
-- pars-betas {M} {N} (_⇛⟨_⟩_ x x₁) = —↠-trans  (par-betas x) (pars-betas x₁)  
       
-}         