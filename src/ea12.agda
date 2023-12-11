open import Lib hiding (lem)

-- ez fuggetlen allitas
-- fuggetlen : (p : ℕ → set) → σ ℕ (λ x → p x → p (suc x))
-- mindenki kap pontot erre a feladatra:
-- (r : ℕ → ℕ → type) → σ ℕ (λ x → r x x → r (suc x) (suc x))

nem : ¬ ((r : ℕ → ℕ → set) → σ ℕ (λ x → σ ℕ (λ y → r x y)) → σ ℕ (λ x → r x x))
nem h = nincsrefl _ (snd (h r (0 , 1 , tt)))
  where
    r : ℕ → ℕ → set
    r 0 1 = ⊤
    r _ _ = ⊥
    nincsrefl : (n : ℕ) → ¬ r n n
    nincsrefl zero = λ x → x
    nincsrefl (suc zero) = λ x → x
    nincsrefl (suc (suc n)) = λ x → x

nem' : ¬ ((r : ℕ → ℕ → set) → r zero zero → r (suc zero) (suc zero))
nem' h = h r tt
  where
    r : ℕ → ℕ → set
    r 0 0 = ⊤
    r _ _ = ⊥
    
     
_≤_ : ℕ → ℕ → set
zero ≤ y = ⊤
suc x ≤ zero = ⊥
suc x ≤ suc y = x ≤ y

nemsym : ¬ ((x y : ℕ) → x ≤ y → y ≤ x)
nemsym sym = sym 0 1 tt

f : σ ℕ (λ x → x ≡ zero → ⊥)
f = 1 , hh
  where
    hh : 1 ≡ 0 → ⊥
    hh ()

ff : ¬ (σ ℕ (λ x → x ≡ x → ⊥))
ff h = snd h refl

-- eddig a canvas kviz

-- eldonthetoseg

decidable' : set → set
decidable' a = a ⊎ ¬ a

-- klasszikus logikaban igaz a kizart harmadik elve:
lem : set₁
lem = (a : set) → a ⊎ ¬ a
-- ez is fuggetlen allitas az agdatol

p : decidable' bool
p = inl true
p' : decidable' ℕ
p' = inl 13
p'' : decidable' ⊥
p'' = inr λ x → x

dec× : {a b : set} → decidable' a → decidable' b → decidable' (a × b)
dec× (inl a)  (inl b)  = inl (a , b)
dec× (inl a)  (inr nb) = inr λ ab → nb (snd ab)
dec× (inr na) (inl b)  = inr λ ab → na (fst ab)
dec× (inr na) (inr nb) = inr λ ab → na (fst ab)

pp : decidable' (⊥ → ⊤)
pp = inl (λ _ → tt)

dec=ℕ : (m n : ℕ) → dec (m ≡ n)
dec=ℕ zero zero = inl refl
dec=ℕ zero (suc n) = inr λ ()
dec=ℕ (suc m) zero = inr λ ()
dec=ℕ (suc m) (suc n) = decsuc _ _ (dec=ℕ m n)
  where
    decsuc : (m n : ℕ) → dec (m ≡ n) → dec (suc m ≡ suc n)
    decsuc m n (inl e) = inl (cong suc e)
    decsuc m n (inr ne) = inr λ e → ne (cong pred' e)

-- stream bool ,  (ℕ → bool),  ℝ, 0.9999999999999... =? 1.0000000000...
hhh : (f g : ℕ → bool) → dec (f ≡ g)
hhh = {!!} -- ilyet nem lehet megadni

postulate
  lem : lem

p=?np : set
p=?np = {!!}

erdekesbool : bool
erdekesbool = case (lem p=?np) (λ _ → true) (λ _ → false)

eldonthetetlen : set₁
eldonthetetlen = (tm : set)(s : tm)(k : tm)(_$_ : tm → tm → tm) →
  ((u v : tm) → (k $ u) $ v ≡ u) →
  ((f g v : tm) → ((s $ f) $ g) $ v ≡ (f $ v) $ (g $ v)) →
  (u v : tm) → u ≡ v
nincsilyen : eldonthetetlen
nincsilyen = {!!}

---------------------------------------------------------------------------------

-- tantargyak: logika, funkcionalis nyelvek (halado haskell), msc-n: nyelvek tipusrendszere(agda), formalis szemantika(coq)

-- kutatas: tipuselmelet kutatoszeminarium, hetente
--          jan.10-en lesz egy tipuselmelet workshop

-- mit kutatunk? bitbucket.org/akaposi/tipuselmelet
--   egyenloseg tipus, data _≡_, refl konstruktor,    (λ x → x + 0) ≡ (λ x → 0 + x)
--   magasabb kategoriaelmelet
