# Típuselmélet (Agda) tantárgy, ELTE, 2023 ősz

Fontos, hogy megfelelő kóddal vedd fel a tárgyat:

 * BSc: IP-18KVSZTM[E|G]
 * MSc: IPM-18sztKVTE[E|G]
 * MSc esti: IPM-18EsztKVTE[E|G]

Előadás oktatója: Kaposi Ambrus (akaposi kukac inf.elte.hu).

Gyakorlatok oktatói:

| kurzus kód     | időpont               | helyszín                          | gyakorlatvezető név | ______@inf.elte.hu |
|----------------|-----------------------|-----------------------------------|---------------------|--------------------|
| 1              | Kedd 19:30-21:00      | Déli Tömb 00-410 (PC 1)           | Török Bálint Bence  | fcjylp             |
| 2              | Hétfo 17:45-19:15     | Déli Tömb 2-218 (komp. alg.)      | Petes Márton        | tx0lwm             |
| 3              | Csütörtök 17:45-19:15 | Déli Tömb 2-124 (Microsoft Labor) | Bense Viktor        | qils07             |
| 4              | Hétfo 19:30-21:00     | Déli Tömb 2-218 (komp. alg.)      | Merth Borbála       | f6tnix             |
| 5              | Kedd 19:30-21:00      | Déli Tömb 2-124 (Microsoft Labor) | Csimma Viktor       | midffj             |

Nagyon fontos, hogy azt a gyakorlatot vedd fel a Neptunban, amelyikre ténylegesen jársz, mert a Canvas automatikusan veszi át az infót a Neptunból.

Létezik egy Típuselmélet 2023 ősz nevű MS Teams csoport, ahol érdemes a típuselméletről beszélgetni, a csatlakozáshoz a kód: 2my8f96. A gyakorlatvezetőknek való email írás helyett itt érdemes kérdéseket feltenni (mások is látják a kérdést/választ, hamarabb kap az ember választ).

Követelmények:

 * Előadásokra Canvas kvíz.
 * Gyakorlatok elején mikrozh Agdában, a házi feladatok a felkészülést segítik.
 * Számítógépes vizsga a vizsgaidőszakban. [Példa vizsga](https://bitbucket.org/akaposi/ttt/raw/master/2022aut/exampleExam.agda)

A gyakorlati jegy a mikrozh-kból áll össze, mindegyikre 0 vagy 1 pontot lehet kapni. Ponthatárok:

| pontszám  | jegy |
|-----------|------|
| 0-4.999   | 1    |
| 5-6.249   | 2    |
| 6.25-7.49 | 3    |
| 7.5-8.749 | 4    |
| 8.75-     | 5    |

Vizsgázni az jöhet, akinek a Canvas kvízek átlaga 50% fölött van és van gyakorlati jegye.

Kötelező irodalom:

 * [Thorsten Altenkirch. Tao of types](http://www.cs.nott.ac.uk/~psztxa/mgs.2021)

Ajánlott irodalom:

 * [Homotopy Type Theory book](http://saunders.phil.cmu.edu/book/hott-online.pdf) (especially Chapter 1 Type theory)
 * [Egbert Rijke. Introduction to homotopy type theory](https://arxiv.org/pdf/2212.11082)
 * [Daniel P. Friedman and David Thrane Christiansen. The little typer](https://thelittletyper.com)
 * [Edwin Brady. Type-driven development with Idris](https://www.manning.com/books/type-driven-development-with-idris)
 * [Kaposi Ambrus. Bevezetés a homotópia-típuselméletbe](https://akaposi.github.io/hott_bevezeto.pdf) (magyar)
 * [Martin Hofmann. Syntax and Semantics of Dependent Types](https://www.tcs.ifi.lmu.de/mitarbeiter/martin-hofmann/pdfs/syntaxandsemanticsof-dependenttypes.pdf)
 * [Ambrus Kaposi. Type systems course notes](https://bitbucket.org/akaposi/typesystems/raw/master/src/main.pdf)

## Előzetes tematika

A Tao könyv fejezetei vannak hivatkozva.

|  het | eloadas                                                           | gyakorlat                        |
|------|-------------------------------------------------------------------|----------------------------------|
|    1 | bevezeto, fuggvenyek (beepitett ℕ peldaval)                       | Emacs, Agda hasznalat,           |
|      | 2.2. identity, composition, polymorphism                          | egyszeru fgv-ek beepitett Nat-on |
|    2 | λ-kalkulus es veges tipusok, Bool=⊤+⊤ mint alkalmazas             | finite type iso                  |
|      | 2.3. λ-calculus                                                   | Bool beepitettkent               |
|      | 2.4 combinatory logic                                             |                                  |
|      | 2.5 products, sums, finite types                                  |                                  |
|      | tipuslevezetes szabalyok alapjan                                  |                                  |
|    3 | induktiv tipusok data-val megadva, Bool-t is elmondani            | induktiv tipusok                 |
|      | 4.1-4.2 inductive types: Nat, Maybe, Ackermann, iterator-recursor |                                  |
|      | 4.3 List, Expr, RoseTree, (Ord)                                   |                                  |
|    4 | induktiv tipusok ertelmessegenek kriteriuma, koinduktiv tipusok   | pozitivitas, koinduktiv tipusok  |
|      | 4.4 positivity, Λ                                                 |                                  |
|      | 4.5 coinductive types: stream, conat                              |                                  |
|      | (4.6 functorial semantics)                                        |                                  |
|    5 | fuggo tipusok                                                     | vec, fin                         |
|      | 5.1 Vec                                                           |                                  |
|      | 5.2 Fin, Vec indexelese                                           |                                  |
|      | 5.3 Π es Σ                                                        |                                  |
|    6 | fuggo tipusok                                                     | fin                              |
|      | 5.4 relating simple and dependent type formers                    |                                  |
|      | 5.5 arithmetic of types `(Fin (m+n) ≅ Fin m ⊎ Fin n)`             |                                  |
|    7 | klasszikus logika, predikutumok, relaciok, elsorendu logika       | propositional logic              |
|      | 3.1 Boolean logic                                                 |                                  |
|      | 3.2 prop as types                                                 |                                  |
|      | 6.1 predicates and quantifiers                                    |                                  |
|    8 | meg predikatumok es relaciok                                      | predicate logic                  |
|      | 6.2 first order logical equivalences                              |                                  |
|      | 6.3 equality                                                      |                                  |
|    9 | indukcio ℕ-en                                                     | properties of div,*              |
|      | 6.4 properties of addition                                        |                                  |
|   10 | equational reasoning                                              | equational reasoning             |
|   11 | induktiv tipusok tovabbi tulajdonsagai: konstruktorok             | data konstruktorok inj, diszj    |
|      | injektivitasa, diszjunktsaga, egyenloseg eldonthetosege           | eldontheto egyenlosegek          |
|      |                                                                   |                                  |
| TODO | klasszikus vs. konstruktiv logika (a,b irrac, a^b rac)            |                                  |
|      | parametricitas, Reynolds fabula                                   |                                  |
|      |                                                                   | f:Bool→Bool-ra f∘f∘f=f           |
|      | ellenpelda relaciok                                               | ellenpelda relaciok, fuggvenyek  |
|      |                                                                   | pigeonhole principle             |
|      | delay monad                                                       | delay monad                      |
|      | oszthatosag, ha `d|x` es `d|y`, akkor `d|x+y`                     |                                  |
|      | ⊤ ≠ ⊤ ⊎ ⊤                                                         |                                  |

## Bevezető és kivezető szabályok

| tipus | bevezető (ha ez a Goal) | eliminációs (ha van egy t nevű feltétel vagy korábbról ismert definíció) |
|-------|----------------|--------------------------------------------------------------|
| ⊥     |                | exfalso t                                                    |
| ⊤     | tt             |                                                              |
| ⊎     | inl ?, inr ?   | case t ? ?                                                   |
| ×     | ? , ?          | fst t, snd t                                                 |
| →     | λ x → ?        | t ?                                                          |
|       |                |                                                              |
| Bool  | true,false     | if t then ? else ?                                           |
| ℕ     | zero,suc       | iteNat ? ? t, recNat ? ? t                                   |
