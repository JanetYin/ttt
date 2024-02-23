open import Agda.Builtin.Nat renaming (Nat to ℕ)

-- Véges típusok
-- Mitől lesz egy típus véges? => Véges számú eleme van, azaz |A| < ∞
-- Milyen véges típusokat ismerünk imperatív nyelvekből?
-- Bool = két elemű típus, true false értékekkel

--           v típust definálunk
data Bool : Set where
-- konstruktor = az egy olyan primitív függvény aminek nincsen számítási szabálya
-- érdemes nem függvényként gondolni rá
-- ez az amire minteillesztünk
-- felsoroljuk milyen értékeket vehetünk fel
  true  : Bool
  false : Bool

-- Mintaillesztés
-- C-c C-c ENTER = felveszi az összes paramétert
-- C-c C-c <paramnév> = mintailleszt
ifThenElse : {A : Set} → Bool → A → A → A
ifThenElse true a₁ a₂ = a₁
ifThenElse false a₁ a₂ = a₂


-- Milyen véges típusok vannak még?
-- Ha van két elemű típus, akkor kéne 1 eleműnek lennie
-- \top = ⊤
data ⊤ : Set where
  tt : ⊤

-- Nagyon izgalmas típus
top : ⊤
top = tt -- más nem lehet, bizonyítható szabály, hogy ∀ t : ⊤. t = tt
-- | ⊤ | = 1

-- Izgalmasabb véges típusok
-- Tuple imperatív nyelvekből, formális nevén SZORZAT típus
-- (A, B) típus egyszerre tároljon A-t és B-t
data _×_ (A B : Set) : Set where
  -- Hány konstruktora lehet?
  -- 1, ez nem azt jelenti, hogy | A × B | = 1
  _,_ : A → B → A × B

h : ℕ × Bool
h = 0 , true

-- kapjuk egy tuple-t paraméterül
j : ℕ × Bool → ℕ
-- Mintaillesztés technológia
-- C-c C-c ENTER = felveszi a paramokat
-- C-c C-c <paramnév> ENTER = mintailleszt
j (x , x₁) = x

-- Összeg típus
-- A ⊎ B azt jelenti, hogy vagy A-t vagy B-t tárol
-- az inl és az inr a konstruktorai, amik azt "witnesselik", hogy melyik ágat választottam
-- inl = bal ág
-- inr = jobb ág

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : A → A ⊎ B

k i : Bool ⊎ ℕ
i = inl true
k = inr false

join : {A : Set} → A ⊎ A → A
join (inl x) = x
join (inr x) = x
