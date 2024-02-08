{-

Típuselmélet   Tipuselmélet (ELTE TTK TO)

Kaposi Ambrus, egyetemi docens, Programozási Nyelvek és Fordítóprogramok Tanszék

Kötelezően választható, Számításelmélet

- 16.00-kor pontban kezdunk
- nincs felvetel
- honlapomon link: teaching / tipuselmelet: bitbucket.org/akaposi/ttt

technikai feltetel: Agda--Emacs
(NixOS)

-}

open import Lib

{-
Curry-Howard izomorfizmus
Kategória
ZFC

Per Martin-Löf, type theory, típuselmélet, programozási nyelv
Agda      típuselmélet (70-es évek, Nicolas De Bruijn)
Haskell   System F (polimorf lambda kalkulus, Reynolds, Girard)
Lisp      lambda kalkulus (Church)  (Turing gép) (Schönfinkel kombinátor logika,SK)

t.t.   programozni, matematikai bizonyításokat számítógéppel ellenőrizni
Agda   svéd  típuselmélet-kutatás, legtöbb szolgáltatás (legjobban hasonlít a Haskellhez)
Lean   amer  matematika, Kevin Buzzard, klasszikus
Coq    fran  legfejlettebb, ipari, Google Chrome
Idris  skót  programozás, kezdetleges

kapcsolódó tárgyak: logika, diszkrét matek (algebra), lineáris alg, Haskell, formális nyelvek

elsőrendű logika + halmazelmélet axiómái        Python     0 ∈ ℕ   0 ∈ 1
0={}                    {}
1={{}}                  {{}}
2={{},{{}}}             {{{}}}
3={{},{{},{{}}}}        ...
4={{},{{},{{},{{}}}}}
típuselmélet                                    Java       0 : ℕ

köv.órán Reynolds fabulája

Mi az a függvény?
-}

add2' : ℕ → ℕ  -- Haskell : <-> :: Agda \->
add2' x = x + 2

-- add2 3 =(def) 3 + 2 =(alt.isk) 5

add2 : ℕ → ℕ
add2 = λ x → x + 2   -- \ x -> x + 2

-- f(x) helyett f x
-- f(1+2) helyett f (1 + 2)
-- add2 3 =(def) (λ x → x + 2) 3 =(β redukcio) (x + 2)[x ↦ 3] = 3 + 2 = 5

plus : ℕ → ℕ → ℕ   -- → jobbra zarojelezodik
plus x y = x + y

k : (ℕ → ℕ) → ℕ 
k h = h 4 + h 3

-- k add2 = add2 4 + add2 3 = (4 + 2) + (3 + 2) = 6 + 5 = 11
