open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import plfa.part2.Substitution using (Rename; Subst)
open import plfa.part2.Untyped
  using (_—→_; β; ξ₁; ξ₂; ζ; _—↠_; begin_; _—→⟨_⟩_; _—↠⟨_⟩_; _∎;
  abs-cong; appL-cong; appR-cong; —↠-trans;
  _⊢_; _∋_; `_; #_; _,_; ★; ƛ_; _·_; _[_];
  rename; ext; exts; Z; S_; subst; subst-zero)

infix 2 _⇛_

data _⇛_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  pvar : ∀{Γ A}{x : Γ ∋ A}
      ---------
    → (` x) ⇛ (` x)

  pabs : ∀{Γ}{N N′ : Γ , ★ ⊢ ★}
    → N ⇛ N′
      ----------
    → ƛ N ⇛ ƛ N′

  papp : ∀{Γ}{L L′ M M′ : Γ ⊢ ★}
    → L ⇛ L′
    → M ⇛ M′
      -----------------
    → L · M ⇛ L′ · M′

  pbeta : ∀{Γ}{N N′  : Γ , ★ ⊢ ★}{M M′ : Γ ⊢ ★}
    → N ⇛ N′
    → M ⇛ M′
      -----------------------
    → (ƛ N) · M  ⇛  N′ [ M′ ]

par-refl : ∀{Γ A}{M : Γ ⊢ A} → M ⇛ M
par-refl {Γ} {A} {` x} = pvar 
par-refl {Γ} {★} {ƛ N} = pabs par-refl
par-refl {Γ} {★} {L · M} = papp par-refl par-refl

par-subst-zero : ∀{Γ}{A}{M M′ : Γ ⊢ A}
       → M ⇛ M′
       → par-subst (subst-zero M) (subst-zero M′)
par-subst-zero {M} {M′} p {A} {Z} = p
par-subst-zero {M} {M′} p {A} {S x} = pvar

sub-par : ∀{Γ A B} {N N′ : Γ , A ⊢ B} {M M′ : Γ ⊢ A}
  → N ⇛ N′
  → M ⇛ M′
    --------------------------
  → N [ M ] ⇛ N′ [ M′ ]
sub-par pn pm = subst-par (par-subst-zero pm) pn

_⁺ : ∀ {Γ A}
  → Γ ⊢ A → Γ ⊢ A
(` x) ⁺       =  ` x
(ƛ M) ⁺       = ƛ (M ⁺)
((ƛ N) · M) ⁺ = N ⁺ [ M ⁺ ]
(L · M) ⁺     = L ⁺ · (M ⁺)

par-triangle : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ⇛ N
    -------
  → N ⇛ M ⁺
par-triangle pvar          = pvar
par-triangle (pabs p)      = pabs (par-triangle p)
par-triangle (pbeta p1 p2) = sub-par (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = ƛ _ } (pabs p1) p2) =
  pbeta (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = ` _}   p1 p2) = papp (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = _ · _} p1 p2) = papp (par-triangle p1) (par-triangle p2)


{-

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
diamond-single {Sₛ · .(_ · _) · y · z} {.(_ · _ · z · (y · z))} {Sₛ · .(_ · _) · y · .z} ps (papp (papp (papp T₀ (papp x₂ x₃)) T₀) T₀) = ⟨ (_ · _ · z · (y · z)) , ⟨ papp (papp   (papp x₂ x₃) (T₀ {z }))(T₀ {(y · z) }) , ps ⟩ ⟩ -- ⟨ (x · z · (y · z)) , ⟨ T₀ , {! papp (ps {x' } {y} {z}) ?!} ⟩ ⟩ --⟨ {!   !} , {!   !} ⟩
diamond-single {Sₛ · x · .(K · _ · _) · z} {.(x · z · (K · _ · _ · z))} {.(Sₛ · x · _) · .z} ps (papp (papp T₀ pk) T₀) = ⟨ x · z · (_ · z) , ⟨ (papp (T₀ {x · z}) (papp pk (T₀ {z}))) , ps ⟩ ⟩
diamond-single {Sₛ · x · .(K · _ · _) · z} {.(x · z · (K · _ · _ · z))} {.(Sₛ · _ · _) · .z} ps (papp (papp (papp T₀ x₂) pk) T₀) = ⟨ _ · z · (_ · z) , ⟨ (papp  (papp x₂ (T₀ {z})) (papp pk (T₀ {z}))) , ps ⟩ ⟩ --⟨ {!   !} , {!   !} ⟩
diamond-single {Sₛ · x · .(Sₛ · _ · _ · _) · z} {.(x · z · (Sₛ · _ · _ · _ · z))} {.(Sₛ · x · (_ · _ · (_ · _))) · .z} ps (papp (papp T₀ ps) T₀) = ⟨ (x · z · (_ · _ · (_ · _) · z)) , ⟨ papp (T₀ {x · z}) (papp ps (T₀ {z}) ) , ps ⟩ ⟩
diamond-single {Sₛ · x · .(Sₛ · _ · _ · _) · z} {.(x · z · (Sₛ · _ · _ · _ · z))} {.(Sₛ · _ · (_ · _ · (_ · _))) · .z} ps (papp (papp (papp T₀ x₂) ps) T₀) = ⟨ _ · z · (_ · _ · (_ · _) · z) , ⟨ (papp   (papp x₂ (T₀ {z}))  (papp ps (T₀ {z}))) , ps ⟩ ⟩
diamond-single {Sₛ · x · .(_ · _) · z} {.(x · z · (_ · _ · z))} {.(Sₛ · x · (_ · _)) · .z} ps (papp (papp T₀ (papp x₂ x₃)) T₀) = ⟨ (x · z · (_ · _ · z)) , ⟨ (papp (T₀ {x · z}) (papp (papp x₂ x₃) (T₀ {z}))) , ps ⟩ ⟩
diamond-single {Sₛ · x · .(_ · _) · z} {.(x · z · (_ · _ · z))} {.(Sₛ · _ · (_ · _)) · .z} ps (papp (papp (papp T₀ x₄) (papp x₂ x₃)) T₀) = ⟨ (_ · z · (_ · _ · z)) , ⟨ (papp  (papp x₄ (T₀ {z})) (papp (papp x₂ x₃) (T₀ {z}))) , ps ⟩ ⟩ ----⟨ {!   !} , {!  !} ⟩ -- ⟨ (_ · _ · z) , ⟨ {! papp x₁ x₂   !} , {!   !} ⟩ ⟩
diamond-single {Sₛ · x · y · .(K · M' · _)} {.(x · (K · M' · _) · (y · (K · M' · _)))} {.(Sₛ · x · _) · M'} ps (papp (papp T₀ x₂) pk) = ⟨ x · _ · (_ · _) , ⟨ papp (papp (T₀ {x}) pk) (papp x₂ pk) , ps ⟩ ⟩
diamond-single {Sₛ · x · y · .(K · M' · _)} {.(x · (K · M' · _) · (y · (K · M' · _)))} {.(Sₛ · _ · _) · M'} ps (papp (papp (papp T₀ x₃) x₂) pk) = ⟨ _ · _ · (_ · _) , ⟨ papp (papp x₃ pk) (papp x₂ pk) , ps ⟩ ⟩
diamond-single {Sₛ · x · y · .(Sₛ · _ · _ · _)} {.(x · (Sₛ · _ · _ · _) · (y · (Sₛ · _ · _ · _)))} {.(Sₛ · x · _) · .(_ · _ · (_ · _))} ps (papp (papp T₀ x₂) ps) = ⟨ _ · (_ · _ · (_ · _)) · (_ · (_ · _ · (_ · _))) , ⟨ (papp (papp (T₀ {x}) ps) (papp x₂ ps)) , ps ⟩ ⟩
diamond-single {Sₛ · x · y · .(Sₛ · _ · _ · _)} {.(x · (Sₛ · _ · _ · _) · (y · (Sₛ · _ · _ · _)))} {.(Sₛ · _ · _) · .(_ · _ · (_ · _))} ps (papp (papp (papp T₀ x₃) x₂) ps) = ⟨ _ · (_ · _ · (_ · _)) · (_ · (_ · _ · (_ · _))) , ⟨ (papp (papp x₃ ps) (papp x₂ ps)) , ps ⟩ ⟩ --⟨ {!   !} , {!   !} ⟩
diamond-single {Sₛ · x · y · .(_ · _)} {.(x · (_ · _) · (y · (_ · _)))} {.(Sₛ · x · _) · .(_ · _)} ps (papp (papp T₀ x₂) (papp x₃ x₄)) = ⟨ (_ · (_ · _) · (_ · (_ · _))) , ⟨ (papp (papp (T₀ {x}) (papp x₃ x₄)) ( papp x₂ (papp x₃ x₄))) , ps ⟩ ⟩
diamond-single {Sₛ · x · y · .(_ · _)} {.(x · (_ · _) · (y · (_ · _)))} {.(Sₛ · _ · _) · .(_ · _)} ps (papp (papp (papp T₀ x₅) x₂) (papp x₃ x₄)) = ⟨ (_ · (_ · _) · (_ · (_ · _))) , ⟨ ((papp (papp x₅ (papp x₃ x₄)) ( papp x₂ (papp x₃ x₄)))) , ps ⟩ ⟩ -- ⟨ L' · M' , ⟨ (Trans_tri ps  (papp x₁ x₂)) , T₀ ⟩ ⟩
diamond-single {(L · M)} {(L' · M')} {(L · M)} (papp x x₁) T₀ = ⟨ L' · M' , ⟨ T₀ , (papp x x₁) ⟩ ⟩
diamond-single {.(K · t₁ · _)} {.(K · t₁) · M'} {t₁} (papp T₀ x₁) pk = ⟨ t₁ , ⟨ pk , T₀ ⟩ ⟩
diamond-single {.(K · t₁ · _)} {.(K · _) · M'} {t₁} (papp (papp T₀ x₂) x₁) pk = ⟨ _ , ⟨ pk , x₂ ⟩ ⟩ --⟨ L' · M' , ⟨ T₀ , (Trans_tri pk (papp x x₁)) ⟩ ⟩
diamond-single {Sₛ · f · g · u} {.(Sₛ · f · g) · M'} {.(f · u · (g · u))} (papp T₀ x₁) ps = ⟨ (f · _ · (_ · _)) , ⟨ ps , papp (papp (T₀ {f}) x₁) (papp (T₀ {g}) x₁) ⟩ ⟩
diamond-single {Sₛ · f · g · u} {.(Sₛ · f · _) · M'} {.(f · u · (g · u))} (papp (papp T₀ x₂) x₁) ps = ⟨ (f · _ · (_ · _)) , ⟨ ps , (papp (papp (T₀ {f}) x₁) (papp x₂ x₁)) ⟩ ⟩
diamond-single {Sₛ · f · g · u} {.(Sₛ · _ · _) · M'} {.(f · u · (g · u))} (papp (papp (papp T₀ x₃) x₂) x₁) ps = ⟨ (_ · _ · (_ · _)) , ⟨ ps , (papp (papp x₃ x₁) (papp x₂ x₁)) ⟩ ⟩ --⟨ {!   !} , {!   !} ⟩ --⟨ L' · M' , ⟨ T₀ , Trans_tri ps (papp x x₁) ⟩ ⟩
diamond-single {.K · .K} {K · K} {.K · .K} (papp T₀ T₀) (papp T₀ T₀) = ⟨ (K · K) , ⟨ T₀ , T₀ ⟩ ⟩ --⟨ {!   !} , {!   !} ⟩
diamond-single {.K · .(K · K · _)} {K · K} {L'' · .(K · K · _)} (papp T₀ pk) (papp x₂ T₀) = ⟨ (L'' · K) , ⟨ (papp x₂ T₀) , (papp T₀ pk) ⟩ ⟩
diamond-single {.K · .(K · K · _)} {K · K} {L'' · .K} (papp T₀ pk) (papp x₂ pk) = ⟨ ((L'' · K)) , ⟨ ((papp x₂ T₀)) , T₀ ⟩ ⟩
diamond-single {.K · .(K · K · _)} {K · K} {.K · .(K · K · _)} (papp T₀ pk) (papp T₀ (papp T₀ x₄)) = ⟨ (K · K) , ⟨ T₀ , (papp T₀ pk) ⟩ ⟩
diamond-single {.K · .(K · K · _)} {K · K} {.K · .(K · K · _)} (papp T₀ pk) (papp T₀ (papp (papp T₀ T₀) x₄)) =  ⟨ _ · _ , ⟨ T₀ , (papp T₀ pk) ⟩ ⟩ -- ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ -- ⟨ {!   !} , {!   !} ⟩
diamond-single {.(K · K · _) · .K} {K · K} {.(K · K · _) · .K} (papp pk T₀) (papp T₀ T₀) = ⟨ _ · _ , ⟨ T₀ , (papp  pk T₀) ⟩ ⟩ --{!   !}
diamond-single {.(K · K · _) · .K} {K · K} {.K · .K} (papp pk T₀) (papp pk T₀) = ⟨ _ · _ , ⟨ T₀ , T₀ ⟩ ⟩ --{!   !}
diamond-single {.(K · K · _) · .K} {K · K} {.(K · K · _) · .K} (papp pk T₀) (papp (papp T₀ x₃) T₀) = ⟨ _ · _ , ⟨ T₀ , (papp  pk T₀) ⟩ ⟩ 
diamond-single {.(K · K · _) · .K} {K · K} {.(K · K · _) · .K} (papp pk T₀) (papp (papp (papp T₀ T₀) x₃) T₀) = ⟨ _ · _ , ⟨ T₀ , (papp  pk T₀) ⟩ ⟩ 
diamond-single {.(K · K · _) · .(K · K · _)} {K · K} {L'' · M''} (papp pk pk) (papp x₂ x₃) = {!   !} -- ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩
diamond-single {.K · .Sₛ} {K · Sₛ} {.K · .Sₛ} (papp T₀ T₀) (papp T₀ T₀) = {!   !}
diamond-single {.K · .(K · Sₛ · _)} {K · Sₛ} {.K · .(K · Sₛ · _)} (papp T₀ pk) (papp T₀ T₀) = {!   !}
diamond-single {.K · .(K · Sₛ · _)} {K · Sₛ} {.K · .Sₛ} (papp T₀ pk) (papp T₀ pk) = {!   !}
diamond-single {.K · .(K · Sₛ · _)} {K · Sₛ} {.K · .(_ · _)} (papp T₀ pk) (papp T₀ (papp x₃ x₄)) = {!   !}
diamond-single {.(K · K · _) · .Sₛ} {K · Sₛ} {L'' · M''} (papp pk T₀) (papp x₂ x₃) = {!   !}
diamond-single {.(K · K · _) · .(K · Sₛ · _)} {K · Sₛ} {L'' · M''} (papp pk pk) (papp x₂ x₃) = {!   !}
diamond-single {L' · M'} {K · (M · M₁)} {L'' · M''} (papp x x₁) (papp x₂ x₃) = {!   !}
diamond-single {L' · M'} {Sₛ · K} {L'' · M''} (papp x x₁) (papp x₂ x₃) = {!   !}
diamond-single {L' · M'} {Sₛ · Sₛ} {L'' · M''} (papp x x₁) (papp x₂ x₃) = {!   !}
diamond-single {L' · M'} {Sₛ · (M · M₁)} {L'' · M''} (papp x x₁) (papp x₂ x₃) = {!   !}
diamond-single {L' · M'} {L · L₁ · K} {L'' · M''} (papp x x₁) (papp x₂ x₃) = {!   !}
diamond-single {L' · M'} {L · L₁ · Sₛ} {L'' · M''} (papp x x₁) (papp x₂ x₃) = {!   !}
diamond-single {L' · M'} {L · L₁ · (M · M₁)} {L'' · M''} (papp x x₁) (papp x₂ x₃) = {!   !} 

-}