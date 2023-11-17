open import Lib
open import Lib.Containers.Vector hiding (take)

-- Nézd meg a gy05-ből, amit üresen hagytunk.

----------------------------------------------

-- Vedd a vektor első i elemét. Miért az a típusszignatúra, ami?
take : ∀{i}{A : Set i}{n : ℕ} -> (i : Fin (suc n)) -> Vec A n -> Vec A (toℕ i)
take = {!!}

-- Milyen rejtett paramétert kell beírni a lyukba,
-- hogy jó típusú Fint kapjunk?
which : Fin 5
which = suc (suc (suc (zero {{!!}})))

-- Ez picit előremutat:
-- írj függvényt, ami egy Fint felemel egy hosszabb Finbe.
-- Pl. inj₁f {3} {5} (suc (suc zero)) a Fin 3-as 2-ből a Fin 8-as 2-t állítja elő.
inj₁f : {m n : ℕ} -> Fin m -> Fin (m + n)
inj₁f = {!!}

-- Kísérletezz: milyen számokat tudsz a bal oldalra beírni? Miért?
ΣFin : Σ ℕ Fin
ΣFin = {!!} , suc (suc (suc zero))

-- Olyan hosszú Fineket lehet megadni, ami a vektor hossza is.
-- Hogyan lehetne ezt kijavítani?
-- Itt is kísérletezz, miket fogad el és miket nem.
-- ΣVecFin : Σ ℕ (λ n -> Vec (Fin n) n)
-- ΣVecFin = 3 , suc (suc zero) ∷ zero ∷ suc (suc (suc zero)) ∷ []

-- Ha van időd, nézd meg a fines feladatokat a következő gyakorlati fájlból (gy06.agda).
