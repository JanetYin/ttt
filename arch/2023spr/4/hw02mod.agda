open import lib

-- írj függvényt az alábbi típusokkal:
f1 : ℕ → (ℕ → ℕ) --hány különböző jelentésűt lehet megadni?
f1 = {!!}
f2 : {A B : Set} → B → (A → B) --és itt?
f2 = {!!}

f3 : (ℕ → Bool → ℕ) → (ℕ → ℕ) --és itt?
f3 f = λ x → x + f x true
f4 : {A B C : Set} → (A → B → C) → A → C --és itt? --legyen A = ⊤, B = ⊥ és C = ⊥ 
f4 f a = f a {!!}

f5 : ℕ → ℕ
f5 = {!!}
f6 : {A B : Set} → A → B --és itt?
f6 = {!!}

f7 : {A B C : Set} → A → B → C → A
f7 = {!!}

-- töltsd ki a lyukat (a bal oldalt ne változtasd):
f8 f8' : {A B : Set} → A → B → A → B → A
f8  a1 _  = λ _  _ → a1
f8' _  _  = λ a2 _ → a2
-- hány különböző jelentésűt lehet megadni?


-- írj függvényt, ami egy kétparaméteres függvényt vár (tetszőleges típussal) és felcseréli a két paraméter sorrendjét
-- a típusszignatúrát is neked kell kitalálni!
flip : {!!}
flip = {!!}

-- írj függvényt, ami B → C és egy A → B típusú függvényt vár (ahol A, B, C tetszőleges Set), és visszaadja ezek kompozícióját
-- a típusszignatúrát is neked kell kitalálni!
fourtimes : {!!}
fourtimes = {!!}

-- ez az egyelemű típus: ⊤
-- az egyetlen eleme: tt

-- azonosak-e az alábbiak:
e1 e2 : Bool ⊎ Bool
e1 = inl true
e2 = inr true

-- azonosak-e az alábbiak:
e3 e4 : Bool × Bool
e3 = true , false
e4 = false , true

neq : (e3 ≡ e4) → ⊥
neq ()

-- picit a következő órára előre (zh-ban nem ilyen lesz, de segít megérteni az előző órait is):
-- hány különböző eleme van a ⊤ × Bool típusnak? add is meg őket!
txb1 txb2 : ⊤ × Bool
txb1 = tt , true
txb2 = tt , false

-- hány különböző eleme van a ⊤ ⊎ Bool típusnak? add is meg őket!
