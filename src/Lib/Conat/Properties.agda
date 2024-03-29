{-# OPTIONS --safe --guardedness #-}

module Lib.Conat.Properties where

open import Lib.Conat.PatternSynonym
open import Lib.Conat.Type
open import Lib.Conat.Base
open import Lib.Conat.Literals
open import Lib.Conat.Bisimulation
open import Lib.Unit.Type
open import Lib.Empty.Type
open import Lib.Equality.Type

open import Lib.Maybe.Type

instance
  isPropIsNotZero∞ : {n : ℕ∞} → ⦃ p1 p2 : IsNotZero∞ n ⦄ → p1 ≡ p2
  isPropIsNotZero∞ {n} with pred∞ n
  ... | just x = refl

reflℕ∞ : (x : ℕ∞) → x ≈ℕ∞ x
reflℕ∞' : (x : Maybe ℕ∞) → x ≈ℕ∞′′ x
reflℕ∞' zero∞ = tt
reflℕ∞' (suc∞ b) = reflℕ∞ b
prove (reflℕ∞ x) = reflℕ∞' (pred∞ x)

symℕ∞ : {x y : ℕ∞} → x ≈ℕ∞ y → y ≈ℕ∞ x
symℕ∞' : {x y : Maybe ℕ∞} → x ≈ℕ∞′′ y → y ≈ℕ∞′′ x
symℕ∞' {zero∞} {zero∞} e = _
symℕ∞' {suc∞ x} {suc∞ y} e = symℕ∞ {x} {y} e
prove (symℕ∞ {x} {y} e) = symℕ∞' (prove e)

transℕ∞ : {x y z : ℕ∞} → x ≈ℕ∞ y → y ≈ℕ∞ z → x ≈ℕ∞ z
transℕ∞' : {x y z : Maybe ℕ∞} → x ≈ℕ∞′′ y → y ≈ℕ∞′′ z → x ≈ℕ∞′′ z
transℕ∞' {zero∞} {zero∞} e1 e2 = e2
transℕ∞' {suc∞ x} {suc∞ y} {suc∞ z} e1 e2 = transℕ∞ e1 e2
prove (transℕ∞ e1 e2) = transℕ∞' (prove e1) (prove e2)

transℕ∞Reflˡ : {x y : ℕ∞}(e : x ≈ℕ∞ y) → transℕ∞ (reflℕ∞ x) e ≈ℕ∞ₚᵣ e
transℕ∞Reflˡ' : {x y : Maybe ℕ∞}(e : x ≈ℕ∞′′ y) → transℕ∞' (reflℕ∞' x) e ≈ℕ∞'ₚᵣ e
transℕ∞Reflˡ' {zero∞} {zero∞} e = _
transℕ∞Reflˡ' {suc∞ x} {suc∞ y} e = transℕ∞Reflˡ {x} {y} e
prove-eq (transℕ∞Reflˡ {x} {y} e) = transℕ∞Reflˡ' {pred∞ x} {pred∞ y} (prove e)

transℕ∞Reflʳ : {x y : ℕ∞}(e : x ≈ℕ∞ y) → transℕ∞ e (reflℕ∞ y) ≈ℕ∞ₚᵣ e
transℕ∞Reflʳ' : {x y : Maybe ℕ∞}(e : x ≈ℕ∞′′ y) → transℕ∞' e (reflℕ∞' y) ≈ℕ∞'ₚᵣ e
transℕ∞Reflʳ' {zero∞} {zero∞} e = _
transℕ∞Reflʳ' {suc∞ x} {suc∞ y} e = transℕ∞Reflʳ {x} {y} e
prove-eq (transℕ∞Reflʳ {x} {y} e) = transℕ∞Reflʳ' {pred∞ x} {pred∞ y} (prove e)

instance
  ≡→≈ℕ∞ : {a b : ℕ∞} → ⦃ a ≡ b ⦄ → a ≈ℕ∞ b
  ≡→≈ℕ∞ {a} ⦃ refl ⦄ = reflℕ∞ a

  ≡→≈ℕ∞′′ : {a b : Maybe ℕ∞} → ⦃ a ≡ b ⦄ → a ≈ℕ∞′′ b
  ≡→≈ℕ∞′′ {a} ⦃ refl ⦄ = reflℕ∞' a

0=0 : 0 ≈ℕ∞ pred∞'' zero∞
prove 0=0 = _

∞+1≡∞ : succ∞ ∞ ≈ℕ∞ ∞
prove ∞+1≡∞ = reflℕ∞ ∞

n+∞≡∞ : ∀ n → n + ∞ ≈ℕ∞ ∞
n+'∞≡∞′ : ∀ n → n +' ∞ ≈ℕ∞′′ suc∞ ∞
n+'∞≡∞′ zero∞ = reflℕ∞ ∞
n+'∞≡∞′ (suc∞ n) = n+∞≡∞ n
prove (n+∞≡∞ n) = n+'∞≡∞′ (pred∞ n)

∞+n≡∞ : ∀ n → ∞ + n ≈ℕ∞ ∞
∞+'n≡∞′ : ∀ n → suc∞ ∞ +' n ≈ℕ∞′′ suc∞ ∞
prove (∞+'n≡∞′ n) = ∞+n≡∞ n
prove (∞+n≡∞ n) = ∞+n≡∞ n

idl+ : (n : ℕ∞) → 0 + n ≈ℕ∞ n
prove (idl+ n) = reflℕ∞' (pred∞ n)

idr+ : ∀ n → n + 0 ≈ℕ∞ n
idr+' : ∀ n → n +' 0 ≈ℕ∞′′ n
prove (idr+ n) = idr+' (pred∞ n)
idr+' zero∞ = tt
idr+' (suc∞ b) = idr+ b

weakenℕ∞ : (a b : ℕ∞) → .(e : IsNotZero∞ a) → IsNotZero∞ (a + b)
weakenℕ∞ a b e with pred∞ a
... | suc∞ _ = tt

instance
  JustIsNotZero∞ : {n n' : ℕ∞} → .⦃ pred∞ n ≈ℕ∞′′ just n' ⦄ → IsNotZero∞ n
  JustIsNotZero∞ {n} with pred∞ n
  ... | suc∞ _ = tt

  JustIsNotZero∞′′ : {n n' : ℕ∞} → .⦃ pred∞ n ≡ just n' ⦄ → IsNotZero∞ n
  JustIsNotZero∞′′ {n} = JustIsNotZero∞ {n}

+-injectiveʳ : (a b c : ℕ∞) → a ≈ℕ∞ b → a + c ≈ℕ∞ b + c
+-injectiveʳ' : (a b : Maybe ℕ∞)(c : ℕ∞) → a ≈ℕ∞′′ b → a +' c ≈ℕ∞′′ b +' c
+-injectiveʳ' zero∞ zero∞ c e = reflℕ∞' (pred∞ c)
+-injectiveʳ' (suc∞ a) (suc∞ b) c e = +-injectiveʳ a b c e
prove (+-injectiveʳ a b c e) = +-injectiveʳ' (pred∞ a) (pred∞ b) c (prove e)

+-injectiveˡ : (a b c : ℕ∞) → a ≈ℕ∞ b → c + a ≈ℕ∞ c + b
+-injectiveˡ' : (a b : ℕ∞)(c : Maybe ℕ∞) → a ≈ℕ∞ b → c +' a ≈ℕ∞′′ c +' b
+-injectiveˡ' a b zero∞ e = prove e
+-injectiveˡ' a b (suc∞ c) e = +-injectiveˡ a b c e
prove (+-injectiveˡ a b c e) = +-injectiveˡ' a b (pred∞ c) e
