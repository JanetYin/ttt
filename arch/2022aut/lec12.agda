open import lib

-- ez az eloadas 5 perccel rovidebb

-- osszeadas tulajdonsagai, egyenlosegi erveles

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

transp : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
transp P refl p = p

idl : (n : ℕ) → zero + n ≡ n
idl = λ n → refl

idr : (n : ℕ) → n + zero ≡ n
idr zero = refl
idr (suc n) = cong suc (idr n)

ass : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass zero n o = refl
ass (suc m) n o = cong suc (ass m n o)

comm-helper : (n m : ℕ) → suc n + m ≡ n + suc m
comm-helper zero m = refl
comm-helper (suc n) m = cong suc (comm-helper n m)

comm : (m n : ℕ) → m + n ≡ n + m
comm zero    n = sym (idr n)
comm (suc m) n = trans (cong suc (comm m n)) (comm-helper n m)
-- x = suc (m + n)
-- y = suc (n + m)
-- z = n + suc m

egyenlet : (m n : ℕ) → (m + m) + (n + 0) ≡ m + (n + m)
egyenlet m n = trans 
-- (m + m) + (n + 0)
                         (cong (λ z → m + m + z) (idr n))
-- (m + m) + n
                         (trans (ass m m n)
-- m + (m + n)
                         (cong (m +_) (sym (comm n m))))
-- m + (n + m)

dist : (m n o : ℕ) → m * (n + o) ≡ m * n + m * o
dist zero n o = refl
dist (suc m) n o = trans
  (cong (n + o +_) (dist m n o))
  (trans (ass n o (m * n + m * o))
  (trans (sym (cong (n +_) (ass o (m * n) (m * o))))
  (trans (cong (λ z → n + (z + m * o)) (comm o (m * n)))
  (trans (cong (n +_) (ass (m * n) o (m * o)))
  (sym (ass n (m * n) (o + m * o)))))))

[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 m n = trans
  (dist (m + n) m n)
  {!!}

-- negativ allitasok szamokrol, pl. 
nemnem12 : ¬ ((n : ℕ) → ¬ (n ≡ 1) → n ≡ 2)
nemnem12 H = 0≠2 (H 0 (λ ()))
  where
    0≠2 : ¬ (0 ≡ 2)
    0≠2 = λ ()
  
nemnem12' : ¬ ((n : ℕ) → ¬ (n ≡ 1) → n ≡ 2)
nemnem12' H with H 0 (λ ())
nemnem12' H | ()

{-
reklam: akinek tetszik az Agda, lehet TDK-t / MSc diplomamunkat csinalni
- kis tipuselmelet kutatocsoport: en, Kovacs Andras, Rafael Bocquet, Vegh Tamas, Bense Viktor, Csimma Viktor
- tovabbi ismeret: MSc-n: nyelvek tipusrendszere, formalis szemantika
                   BSc-n is: funkcionalis nyelvek
                   tipuselmelet kutatoszeminarium: https://bitbucket.org/akaposi/tipuselmelet
                   cikkek
                   konyvek: Homotopy Type Theory <- matematikusoknak tipuselmelet hasznalat bevezeto
                   kategoriaelmelet: Benjamin Pierce: Basic Category Theory for Computer Scientists
                                     Steve Awodey: Category theory
mik a fontos jelenlegi kutatasi problemak?
- tipuselmeletben formalizalni a matematikai bizonyitasokat
  - Lean bizonyito rendszer (klasszikus)
  ? konstruktivan formalizalni a matematikat: Errett Bishop konyve
- 
-}

T : Bool → Set
T true  = ⊤
T false = ⊥

data Reflects {p} (P : Set p) : Bool → Set p where
  ofʸ : ( p :   P) → Reflects P true
  ofⁿ : (¬p : ¬ P) → Reflects P false

injsuc : {a b : ℕ} → suc a ≡ suc b → a ≡ b
injsuc refl = refl

_≟_ : (a b : ℕ) → (a ≡ b) ⊎ ¬ (a ≡ b)
zero ≟ zero = inl refl
zero ≟ suc b = inr λ ()
suc a ≟ zero = inr λ ()
suc a ≟ suc b with a ≟ b
... | inl e = inl (cong suc e)
... | inr ne = inr λ e → ne (injsuc e)

==refl : (a : ℕ) → (a == a) ≡ true
==refl zero = refl
==refl (suc a) = ==refl a

≠==false : (a b : ℕ) → (¬ (a ≡ b)) → (a == b) ≡ false
≠==false zero zero ne with ne refl
... | ()
≠==false (suc a) (suc b) ne = ≠==false a b λ e → ne (cong suc e)
≠==false zero (suc b) ne = refl
≠==false (suc b) zero ne = refl

≡Equiv== : {a b : ℕ} → (Reflects (a ≡ b) (a == b))
≡Equiv== {a}{b} with a ≟ b
... | inl refl = transp (Reflects (a ≡ a)) (sym (==refl a)) (ofʸ refl)
... | inr x = transp (Reflects (a ≡ b)) (sym (≠==false a b x)) (ofⁿ x)
