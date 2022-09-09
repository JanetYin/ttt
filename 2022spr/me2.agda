-- http://www.cs.nott.ac.uk/~psztxa/mgs.2021/prop-logic.pdf

module me2 where

open import me1sol

module tmp where
  -- FEL: add meg a Bool tipust (az eddigi tipusok felhasznalasaval, nem data-val), es a hozza tartozo muveleteket.
  Bool : Set
  Bool = {!!}

  true false : Bool
  true = {!!}
  false = {!!}

  if_then_else_ : Bool → A → A → A
  if b then a else a' = {!!}
  -- Alt-. elugrik a definiciohoz

  -- FEL: mutasd meg egyenlosegi ervelessel, hogy
  -- 1. if true  then a else a' =(if_then_else_ def) case (λ _ → a) (λ _ → a') (inj₁ tt) =(case def) (λ _ → a) tt =(β) a
  -- 2. if false then a else a' = a'

---------------------------------------------------------------------
-- 3.1. Propositions as booleans
---------------------------------------------------------------------

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
_∣_ = {!!}

-- FEL: bizonyitsd be esetszetvalasztassal _∣_ kommutativitasat!

-- FEL: bizonyisd be az alabbi disztributivitasi torvenyt esetszetvalasztassal: x & (y ∣ z) = (x & y) ∣ (x & z)

-- FEL: bizonyitsd be a disztributivitas alabbi ket specialis esetet egyenlosegi ervelessel:
-- true  & (y ∣ z) = (true  & y) ∣ (true  & z)
-- false & (y ∣ z) = (false & y) ∣ (false & z)

-- FEL: bizonyisd be a masik disztributivitasi torvenyt: x ∣ (y & z) = (x ∣ y) & (x ∣ z)

-- FEL: logikai negacio
!_ : Bool → Bool
!_ = {!!}

-- bizonyisd be az alabbi De Morgan szabalyokat!
-- ! (x & y) = (! x) ∣ (! y)
-- ! (x ∣ y) = (! x) & (! y)

-- FEL: add meg az akkor es csak akkort logikai allitasokra! add meg esetszetvalasztas nelkul is!
_<=>_ : Bool → Bool → Bool
_<=>_ = {!!}
-- megjegyzes: igy adhato meg az egyenloseg klasszikus logikaban

-- FEL: add meg a kizaro vagy (exclusive or) muveletet! add meg esetszetvalasztas nelkul is!
_xor_ : Bool → Bool → Bool
_xor_ = {!!}

-- FEL: add meg az implikacio (kovetkezik / ha, akkor) muveletet!
_=>_ : Bool → Bool → Bool
_=>_ = {!!}

-- FEL (fakultativ): mutasd meg, hogy az alabbi _nor_ muvelettel (Sheffer's stroke) megadhatok az _&_,  _∣_, !_ muveletek! Ellenorizd, hogy tenyleg ugy mukodnek, ahogy kell!
_nor_ : Bool → Bool → Bool
x nor y = ! (x ∣ y)
_&'_ : Bool → Bool → Bool
_&'_ = {!!}
_∣'_ : Bool → Bool → Bool
_∣'_ = {!!}
!'_ : Bool → Bool
!'_ = {!!}

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
∧-comm₁ = {!!}  -- C-c C-,      C-u C-u C-c C-,

-- FEL
∧-comm : P ∧ Q ⇔ Q ∧ P
∧-comm = {!!}

-- FEL
∧-ass : (P ∧ Q) ∧ R ⇔ P ∧ (Q ∧ R)
∧-ass = {!!}

-- FEL
∨-idl : ⊥ ∨ P ⇔ P
∨-idl = {!!}

-- FEL: De Morgan laws (distributivity)
dm₁ : ¬ (P ∨ Q) ⇔ ¬ P ∧ ¬ Q
dm₁ = {!!}
dm₂₂ : ¬ P ∨ ¬ Q ⇒ ¬ (P ∧ Q)
dm₂₂ = {!!}

-- FEL: ezt miert nem lehet belatni? ¬ (P ∧ Q) ⇒ ¬ P ∨ ¬ Q

-- meg feladatok:

-- FEL
∨-ass : (P ∨ Q) ∨ R ⇔ P ∨ (Q ∨ R)
∨-ass = {!!}

∨-comm : P ∨ Q ⇔ Q ∨ P
∨-comm = {!!}

∧-idl : ⊤ ∧ P ⇔ P
∧-idl = {!!}

∨∧-dist : P ∨ (Q ∧ R) ⇔ (P ∨ Q) ∧ (P ∨ R)
∨∧-dist = {!!}

∧∨-dist : P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)
∧∨-dist = {!!}

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
fel1 Ak = {!!}
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
dm₂₁ = {!!}

-- reductio ad absurdo, indirekt bizonyitas
RAA : prop → prop
RAA P = ¬ (¬ P) → P

-- FEL
tnd→raa : TND P → RAA P
tnd→raa = {!!}

-- FEL
nntnd : ¬ (¬ (P ∨ ¬ P))
nntnd = {!!}

-- FEL: hasznald nntnd-t!
raa→tnd : RAA (P ∨ ¬ P) → TND P
raa→tnd = {!!}
