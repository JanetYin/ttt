-- http://www.cs.nott.ac.uk/~psztxa/mgs.2021/prop-logic.pdf

module me2sol where

open import me1sol

module tmp where
  -- FEL: add meg a Bool tipust (az eddigi tipusok felhasznalasaval, nem data-val), es a hozza tartozo muveleteket.
  Bool : Set
  Bool = ⊤ ⊎ ⊤

  true false : Bool
  true = inj₁ tt
  false = inj₂ tt

  if_then_else_ : Bool → A → A → A
  if b then a else a' = case (λ _ → a) (λ _ → a') b -- Alt-. elugrik a definiciohoz

-- case f g (inj₁ a) = f a
-- case f g (inj₂ b) = g b

  -- FEL: mutasd meg egyenlosegi ervelessel, hogy
  -- 1. if true  then a else a' =(if_then_else_ def) case (λ _ → a) (λ _ → a') (inj₁ tt) =(case def) (λ _ → a) tt =(β) a
  -- 2. if false then a else a' = a'

---------------------------------------------------------------------
-- 3.1. Propositions as booleans
---------------------------------------------------------------------

infixl 5 _&_
infixl 3 _∣_
infixr 2 _=>_
infix 1 _<=>_

data Bool : Set where
  true false : Bool

-- es muvelet
_&_ : Bool → Bool → Bool
true  & y = y
false & y = false

{-
Az _&_ kommutativitasanak (x & y = y & x) bizonyitasa esetszetvalasztassal (igazsagtabla) es egyenlosegi ervelessel:
Negy eset van attol fuggoen, hogy x ill. y true vagy false erteket vesz fel:

| x     | y     | x & y  | y & x  |    egyenlosegi erveles az adott esetben:
|-------|-------|--------|--------|
| true  | true  | true   | true   |    true & true =(refl) true & true
| true  | false | false  | false  |    true & false =(_&_ def) false =(_&_ def) false & true
| false | true  | false  | false  |    false & true =(_&_ def) false =(_&_ def) true & false
| false | false | false  | false  |    false & false =(refl) false & false

Latjuk, hogy x & y = y & x minden sorban, ezzel bebizonyitottuk.
-}

-- FEL: logikai vagy
_∣_ : Bool → Bool → Bool -- \|
true ∣ y = true
false ∣ y = y

-- FEL: bizonyitsd be esetszetvalasztassal _∣_ kommutativitasat!

-- FEL: bizonyisd be az alabbi disztributivitasi torvenyt esetszetvalasztassal: x & (y ∣ z) = (x & y) ∣ (x & z)

-- FEL: bizonyitsd be a disztributivitas alabbi ket specialis esetet egyenlosegi ervelessel:
-- true  & (y ∣ z) = (true  & y) ∣ (true  & z)
-- false & (y ∣ z) = (false & y) ∣ (false & z)

-- FEL: bizonyisd be a masik disztributivitasi torvenyt: x ∣ (y & z) = (x ∣ y) & (x ∣ z)

-- FEL: logikai negacio
!_ : Bool → Bool
! true = false
! false = true

-- bizonyisd be az alabbi De Morgan szabalyokat!
-- ! (x & y) = (! x) ∣ (! y)
-- ! (x ∣ y) = (! x) & (! y)

-- FEL: add meg az akkor es csak akkort logikai allitasokra! add meg esetszetvalasztas nelkul is!
_<=>_ : Bool → Bool → Bool
x <=> y = x & y ∣ ! x & ! y
-- megjegyzes: igy adhato meg az egyenloseg klasszikus logikaban

-- FEL: add meg a kizaro vagy (exclusive or) muveletet! add meg esetszetvalasztas nelkul is!
_xor_ : Bool → Bool → Bool
x xor y = x & ! y ∣ ! x & y

-- FEL: add meg az implikacio (kovetkezik / ha, akkor) muveletet!
_=>_ : Bool → Bool → Bool
x => y = ! x ∣ y

-- FEL (fakultativ): mutasd meg, hogy az alabbi _nor_ muvelettel (Sheffer's stroke) megadhatok az _&_,  _∣_, !_ muveletek! Ellenorizd, hogy tenyleg ugy mukodnek, ahogy kell!
_nor_ : Bool → Bool → Bool
x nor y = ! (x ∣ y)
!'_ : Bool → Bool
!' x = x nor x
_&'_ : Bool → Bool → Bool
x &' y = (!' x) nor (!' y)
_∣'_ : Bool → Bool → Bool
x ∣' y = !' (x nor y)

-- "propositions as bools" nem mukodik elsorendben: ha P : ℕ → Bool, nem adhato meg (∀n.P(n)) : Bool

---------------------------------------------------------------------
-- 3.2. Propositions as types
---------------------------------------------------------------------

-- az allitas a bizonyitasainak a halmaza (tipusa); ez konstruktiv logikat ad

prop = Set

_∧_ : prop → prop → prop -- \and
P ∧ Q = P × Q

_∨_ : prop → prop → prop -- \or
P ∨ Q = P ⊎ Q

_⇒_ : prop → prop → prop -- \=>
P ⇒ Q = P → Q

True : prop
True = ⊤

False : prop
False = ⊥

-- rovidites:
¬_ : prop → prop -- \neg
¬ P = P ⇒ False

-- rovidites:
_⇔_ : prop → prop → prop -- \<=>
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)
-- megjegyzes: egyenloseg konstruktiv logikaban

{-
osszefoglalas a logikai osszekotokrol:

| es                  | konjunkcio   | _&_   | _∧_   | _×_ |
| vagy                | diszjunkcio  | _∣_   | _∨_   | _⊎_ |
| kovetkezik          | implikacio   | _=>_  | _⇒_   | _→_ |
| igaz                | verum        | true  | True  | ⊤   |
| hamis               | falsum       | false | False | ⊥   |
| nem                 | negacio      | !_    | ¬_    |     |
| akkor es csak akkor | ekvivalencia | _<=>_ | _⇔_   |     |
-}

infixl 5 _∧_
infixl 3 _∨_
infixr 2 _⇒_
infix 1 _⇔_
variable P Q R : prop

-- FEL
∧-comm₁ : P ∧ Q ⇒ Q ∧ P
∧-comm₁ = λ pq → proj₂ pq , proj₁ pq  -- C-c C-,      C-u C-u C-c C-,

-- FEL
∧-comm : P ∧ Q ⇔ Q ∧ P
proj₁ ∧-comm = ∧-comm₁
proj₂ ∧-comm = ∧-comm₁

-- FEL
∧-ass : (P ∧ Q) ∧ R ⇔ P ∧ (Q ∧ R)
∧-ass = (λ pqr → proj₁ (proj₁ pqr) , (proj₂ (proj₁ pqr) , proj₂ pqr)) , (λ pqr → (proj₁ pqr , proj₁ (proj₂ pqr)) , proj₂ (proj₂ pqr))

-- FEL
∨-idl : ⊥ ∨ P ⇔ P
proj₁ ∨-idl = case case⊥ λ p → p
proj₂ ∨-idl = inj₂

-- FEL: De Morgan laws (distributivity)
dm₁ : ¬ (P ∨ Q) ⇔ ¬ P ∧ ¬ Q
proj₁ dm₁ = λ w → (λ p → w (inj₁ p)) , (λ q → w (inj₂ q))
proj₂ dm₁ = λ w → case (proj₁ w) (proj₂ w)
dm₂₂ : ¬ P ∨ ¬ Q ⇒ ¬ (P ∧ Q)
dm₂₂ = λ w pq → case (λ np → np (proj₁ pq)) (λ nq → nq (proj₂ pq)) w

-- FEL: ezt miert nem lehet belatni? ¬ (P ∧ Q) ⇒ ¬ P ∨ ¬ Q

-- meg feladatok:

-- FEL
∨-ass : (P ∨ Q) ∨ R ⇔ P ∨ (Q ∨ R)
proj₁ ∨-ass = case (case inj₁ (λ q → inj₂ (inj₁ q))) (λ r → inj₂ (inj₂ r))
proj₂ ∨-ass = case (λ p → inj₁ (inj₁ p)) (case (λ q → inj₁ (inj₂ q)) inj₂)

∨-comm : P ∨ Q ⇔ Q ∨ P
proj₁ ∨-comm = case inj₂ inj₁
proj₂ ∨-comm = case inj₂ inj₁

∧-idl : ⊤ ∧ P ⇔ P
proj₁ ∧-idl = proj₂
proj₂ ∧-idl = λ p → tt , p

∨∧-dist : P ∨ (Q ∧ R) ⇔ (P ∨ Q) ∧ (P ∨ R)
proj₁ ∨∧-dist = case (λ p → (inj₁ p , inj₁ p)) (λ qr → inj₂ (proj₁ qr) , inj₂ (proj₂ qr))
proj₂ ∨∧-dist = λ w → case inj₁ (λ q → case inj₁ (λ r → inj₂ (q , r)) (proj₂ w)) (proj₁ w)

∧∨-dist : P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)
proj₁ ∧∨-dist = λ w → case (λ q → inj₁ (proj₁ w , q)) (λ r → inj₂ (proj₁ w , r)) (proj₂ w)
proj₂ ∧∨-dist = case (λ pq → proj₁ pq , inj₁ (proj₂ pq)) (λ pr → proj₁ pr , inj₂ (proj₂ pr))

{-
A1: Ha Aladár busszal utazik, és a busz késik, akkor nem ér oda a találkozóra.
A2: Ha nem ér oda a találkozóra és nem tud telefonálni, akkor nem kapja meg az állást.
A3: Ha rossz a kocsija, akkor busszal kell mennie.
A4: Aladárnak rossz napja van, mert a kocsija nem indul, rossz a telefonja és a busz késik.
BB:  Tehát Aladár nem kapja meg az állást.
-}
postulate
  busszal kesik odaer telefonal megkap rossz-kocsi : prop

A1 A2 A3 A4 BB : prop
A1 = busszal ∧ kesik ⇒ ¬ odaer
A2 = ¬ odaer ∧ ¬ telefonal ⇒ BB
A3 = rossz-kocsi ⇒ busszal
A4 = rossz-kocsi ∧ ¬ telefonal ∧ kesik
--------------------------------------
BB = ¬ megkap

fel1 : A1 ∧ A2 ∧ A3 ∧ A4 ⇒ BB
fel1 Ak = a2 (a1 (a3 (proj₁ (proj₁ a4)) , proj₂ a4) , proj₂ (proj₁ a4))
  where
    a1 : A1
    a1 = proj₁ (proj₁ (proj₁ Ak))
    a2 : A2
    a2 = proj₂ (proj₁ (proj₁ Ak))
    a3 : A3
    a3 = proj₂ (proj₁ Ak)
    a4 : A4
    a4 = proj₂ Ak
-- C-u C-u C-c C-, feloldja az osszes roviditest

{-
FEL:

A1: Ha elmegyünk Pécsre, akkor Hévízre és Keszthelyre is.
A2: Ha nem megyünk Keszthelyre, akkor elmegyünk Hévízre.
A3: Ha elmegyünk Keszthelyre, akkor Pécsre is.
A4: Elmegyünk Keszthelyre vagy nem megyünk el Keszthelyre.
B:  Tehát elmegyünk Hévízre.
-}

---------------------------------------------------------------------
-- 3.3. Classical principles
---------------------------------------------------------------------

-- tertium non datur, law of excluded middle, kizart harmadik elve
TND : prop → prop
TND P = P ∨ ¬ P

-- FEL
dm₂₁ : TND P → ¬ (P ∧ Q) ⇒ ¬ P ∨ ¬ Q
dm₂₁ = case (λ p w → inj₂ λ q → w (p , q)) (λ np _ → inj₁ np)

-- reductio ad absurdo, indirekt bizonyitas
RAA : prop → prop
RAA P = ¬ (¬ P) → P

-- FEL
tnd→raa : TND P → RAA P
tnd→raa = case (λ p _ → p) (λ np nnp → case⊥ (nnp np))

-- FEL
nntnd : ¬ (¬ (P ∨ ¬ P))
nntnd = λ w → w (inj₂ λ p → w (inj₁ p))

-- FEL: hasznald nntnd-t!
raa→tnd : RAA (P ∨ ¬ P) → TND P
raa→tnd = λ raa → raa nntnd
