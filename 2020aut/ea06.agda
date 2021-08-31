module lec.ea6 where

open import lib

{-
f : A → B    u : A
------------------
    f u : B


λ x → suc ((x true) zero)
           \_/\__/
              : Bool
           :Bool → ℕ → ℕ

           \______/ \___/
           : ℕ → ℕ   : ℕ

          \_____________/
              : ℕ

      \_________________/      
          : ℕ

(Bool → ℕ → ℕ) → ℕ	
Bool → (ℕ → ℕ)


-}




f0 f1 f2 f3 f02 f03 f04 : {X : Set} → (X ⊎ X → X ⊎ X)
f0 = λ w → case w (λ x → inj₁ x) (λ x → inj₁ x)
f1 = λ w → case w (λ x → inj₁ x) (λ x → inj₂ x)
f2 = λ w → case w (λ x → inj₂ x) (λ x → inj₁ x)
f3 = λ w → case w (λ x → inj₂ x) (λ x → inj₂ x)
f02 = λ w → f0 (f0 w)
f03 = λ w → f0 (f0 (f0 w))
f04 = λ w → f0 (f0 (f0 (f0 w)))

-- case (inj₁ a) f g = f a
-- case (inj₂ b) f g = g b

-- vegtelen sok ilyen f van, amik, mint programok, kulonbozok de majd
-- kesobb latni fogjuk, hogy ha matematikailag adjuk meg a fuggvenyek
-- "egyenloseget"q, akkor csak 4 lesz.

{-

eddig csak programoztunk, voltak típusaink, típusonként voltak operátaink
mi köze ennek a logikához/bizonyításokhoz/matematikához

bizonyos típusok azok állítások: 

Agda jelölés    programozás                              logika
=======================================================================================
⊤               1-elemű típus, (), unit, void            Igaz(triviálisan bizonyítható)

⊥               (programozásban nem jellemző)            Hamis(bizonyíthatatlan,
                                                               ex falso quodlibet)
                üres típus (? üres union)
                Rust: never

A → B           függvény típus (magasabbrendű)           implikáció(következtetés)
                                 (A → B) → C             (elim: modus ponens) A ⊃ B 

A × B           record típus, szorzat típus,             és, konjunkció, A ∧ B
                struct

A ⊎ B           union, Either                            vagy, diszjunkció, A ∨ B


ha egy A típus állítás, akkor t : A  úgy olvasható t programnak/termnek A típusa van
                                                   t bizonyítja A-t
                                                   (t egy bizonyítás, A állítás/tétel)

    t : ⊥        t ⊥ típusú               t bizonyítja ⊥-ot
-------------    ------------------    ------------------------
exfalso t : A    exfalso t A típusú     exfalso t bizonyítja A-t

t : A → B   u : A     t bemenete A típusú, kimeneet B típusú   u A típusú
-----------------     ---------------------------------------------------
     t u : B                t u az B típusú

t bizonyítja, hogy A-ból következik B          u bizonyítja A-t
---------------------------------------------------------------modus_ponens
              t u azt bizonyítja, hogy B

u:A és v:B     A-t bizonyítja u      B-t bizonyítja v        A₁×A₂-t bizonyítja t
----------     --------------------------------------        --------------------i∈{1,2}
u,v : A×B              A×B-t bizonyítja u,v                   projᵢ t : Aᵢ  

   u : A          t : A⊎B      u : A → C       v : B → C
------------      --------------------------------------
inj₁ u : A⊎B                case t u v : C

a típuselmélet szabályainak (bevezető,eliminációs,számítási,egyediség)
tanulásával egyszerre tanulunk típusrendszert és bizonyításelméletet

true : Bool         <- true-nek semmi köze nincs igaz-hoz (⊤)
true ≠ ⊤, sőt az egyik term, a másik típus
true a kételemű típus (Bool) egyik eleme, kicsit szerencsétlen neve van

Rövidítés:

↔ akkor és csak akkor (logikai ekivalencia)    oda-vissza függvények, adattranszformáció

A ↔ B := (A → B) × (B → A): A implikálja B-t és B implikálja A-t

ℕ nem állítás, de típus
vannak olyan típusok, amik nem állítások
minden állítás típus
t : A 

¬ A := A → ⊥

t : ¬A    t azt bizonyítja, hogy A nem igaz
          t azt bizonyítja, hogy A implikálja hamist

ítéletlogika: ítéletváltozók

Z:=esik az eső                    n<2      ...
M:=otthon maradok                 n=0
P:=esernyőt viszek magammal       n=1
{Z ⊃ M ∨ P, Z, ¬P } |= M
-}

-- curry-uncurry    (A → (B → C)) ↔ (A × B → C)

g1 : {Z M P : Set} → (Z → (M ⊎ P)) → Z → ¬ P → M
g1 = λ w z np → case (w z) (λ m → m) (λ p → exfalso (np p))

-- {¬P ⊃ Q, S ⊃ R, ¬Q ∧ ¬R} |= ¬¬P ∧ ¬S
g2 : {P Q R S : Set} → (¬ P → Q) → (S → R) → (¬ Q × ¬ R) → ¬ ¬ P × ¬ S
g2 = λ npq sr npr → (λ np → proj₁ npr (npq np)) , λ s → proj₂ npr (sr s)

-- {P ⊃ Q ∨ R, R ⊃ ¬P ∧ Q, P ∨ R} |= Q
g3 : {P Q R : Set} → (P → (Q ⊎ R)) → (R → (¬ P × Q)) → P ⊎ R → Q
g3 = λ a b c → case c (λ p → case (a p) (λ q → q) (λ r → proj₂ (b r))) (λ r → proj₂ (b r))

-- különbség a szokásos (klasszikus) logika és a típuselmélet logikája
-- között

-- A → B := B ∨ ¬ A

-- típuselméletben konstruktív logikát csinálunk, nem klasszikusat
-- klasszikus logika := típuselmélet + lem (law of excluded middle, kizárt harmadik elve,
-- tertium non datur)

-- A-t akarom bizonyítani klasszikusan, akkor A helyett azt bizonyítom, hogy LEM → A

-- LEM = ({A : Set} → A ⊎ ¬ A)



