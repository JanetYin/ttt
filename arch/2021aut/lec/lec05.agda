open import lib
{-

λ x → suc (x tt zero) : (𝟚 → ℕ → ℕ) → ℕ

{X : Set}     → X × (X ⊎ X) ↔ (X × X) ⊎ (X × X)	
{X Y Z : Set} → X × (Y ⊎ Z) ↔ (X × Z) ⊎ (Y × X)	
NEM {X : Set} → X × (X ⊎ Y) ↔ X × Y	
{X : Set} → X × (X ⊎ X) ↔ X × X	
{X : Set} → X × (X ⊎ X) → X

{X : Set} → X → X          1
            𝟚 → 𝟚    (λ x → if x then tt else ff) ≠ (λ x → x)
{X : Set} → X → X → X      2
{X : Set} → (X → X) → X    0
{X : Set} → (ℕ → X → X) → (X → 𝟚) → (X → ℕ) → (X → X) → X
f : (⊥ → ⊥) → ⊥   f (λ x → x) : ⊥

{X : Set} → (X → X) → (X → X)   (természetes számok Church-kódolása, feladat, N := {X : Set} → (X → X) → (X → X), zero := ?, suc := ? , rec := ?)
  (λ f → λ x → x)
  (λ f → f) = (λ f → λ x → f x)       (→egyediseg: f = λx→f x)
  (λ f x → f (f x))
  (λ f x → f (f (f x)))
  ....
{X : Set} → X × Y → Y × X

{X : Set} → (X → ⊥) ↔ X	
{X Y Z : Set} → (X × (Y × Z)) ↔ (X × Y)
{X : Set} → (X → ⊥) ↔ ((X → ⊥) × ⊤) ↔ ((X → ⊥) × (⊥ → X))	
{X : Set} → (⊥ → X) ↔ (X ↔ ⊥)	

{X Y Z : Set} → ((X → Y) × (Y → Z)) → (X → Z)	
{X Y Z : Set} → ((X → Y) × (Y → Z)) ↔ (X → Z)	
{X Y Z : Set} → (X → Y) ↔ ((X × Z) → (Y × Z))	

{X : Set} → (X ↔ X)	
{X Y : Set} → (X ↔ Y) = (X → Y) × (Y → X) ↔ (Y → X) × (X → Y) = (Y ↔ X)	

(λ x → π₁ x (π₂ x)) : ((A → B) × A) → B

logika

t : A      t term/program típusa A
bizonyos A-k logikai állítások
t : A      az A állításnak t egy bizonyítása

⊥    Hamis
⊤    Igaz
A∨B  A vagy B
A∧B  A és B
A⇒B  A-ból következik B
¬A   nem A
X,Y,Z  ítéletváltozók (0.rendű logikai változók)


X × X <-> X




-}

{-
Tichler Krisztián példái

A1: Ha nálam van a kapukulcs, akkor ki tudom nyitni a kaput.
A2: Nálam van a kapukulcs.
B:  Ki tudom nyitni a kaput.
-}
l1 : {Kulcs Nyit : Set} → (Kulcs → Nyit) → Kulcs → Nyit
l1 = λ A1 A2 → A1 A2

{-
A1: Ha a benzin elfogyott az autóból, akkor az autó megáll.
A2: Nem fogyott el a benzin.
B:  Tehát az autó nem áll meg.
-}
l2 : {Elf Megall : Set} → (Elf → Megall) → ¬ Elf → ¬ Megall
l2 = λ A1 A2 → λ megall → {!!}


{-
A1: Ha egy egyenesnek nincs közös pontja a síkkal, akkor párhuzamos a síkkal.
A2: Ha egy egyenesnek egynél több közös pontja van a síkkal, akkor illeszkedik rá.
A3: Egy adott egyenes nem párhuzamos egy adott síkkal és nem is illeszkedik rá.
B:  Az adott egyenesnek egy és csak egy közös pontja van az adott síkkal.
-}
l3 : {NincsKozos Parh EgynelTobb Illeszk : Set} →
  (NincsKozos → Parh) → (EgynelTobb → Illeszk) →
  (¬ Parh × ¬ Illeszk) → ¬ NincsKozos × ¬ EgynelTobb
l3 = λ A1 A2 A3 → (λ nincskoz → π₁ A3 (A1 nincskoz)) ,
                  λ egynelt → π₂ A3 (A2 egynelt)

{-
A1: Ha Aladár busszal utazik, és a busz késik, akkor nem ér oda a találkozóra.
A2: Ha nem ér oda a találkozóra és nem tud telefonálni, akkor nem kapja meg az állást.
A3: Ha rossz a kocsija, akkor busszal kell mennie.
A4: Aladárnak rossz napja van, mert a kocsija nem indul, rossz a telefonja és a busz késik.
B:  Tehát Aladár nem kapja meg az állást.
-}
l4 : {Busszal Kesik Odaer Telef Megkap Rossz : Set} →
  (Busszal × Kesik → ¬ Odaer) → 
  (¬ Odaer × ¬ Telef → ¬ Megkap) →
  (Rossz → Busszal) →
  (Rossz × ¬ Telef × Kesik) → ¬ Megkap
l4 = λ A1 A2 A3 A4 → A2 (A1 ((A3 (π₁ A4)) , (π₂ (π₂ A4))) , π₁ (π₂ A4))


-- Agdaban konstruktiv logika van (intuicionista logika)
-- (f : ℕ → 𝟚)

{-
A1: Ha elmegyünk Pécsre, akkor Hévízre és Keszthelyre is.
A2: Ha nem megyünk Keszthelyre, akkor elmegyünk Hévízre.
A3: Ha elmegyünk Keszthelyre, akkor Pécsre is.
B:  Tehát elmegyünk Hévízre.
-}
l5 : {P H K : Set} → (K ⊎ ¬ K) → (P → H × K) → (¬ K → H) → (K → P) → H
l5 = λ kvnk A1 A2 A3 → case kvnk
  (λ k → π₁ (A1 (A3 k)))
  A2
{-
A1: Ha repülővel utazunk, akkor útlevelet is viszünk magunkkal és korán kelünk.
A2: Ha nem kelünk korán, akkor viszünk magunkkal útlevelet.
A3: Ha korán kelünk, akkor aznap repülővel utazunk.
B:  Tehát viszünk magunkkal útlevelet.
(kl)
-}

-- X → ¬ ¬ X

idoutazas : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
idoutazas = λ v → v (ι₂ λ x → v (ι₁ x))
{-    →      ×       ⊎       ⊥         ⊤
bev   λ      _,_     ι₁,ι₂            triv        lem
elim  appl   π₁,π₂   case   exfalso
-}
