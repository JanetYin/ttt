# Típuselmélet (Agda) tantárgy, ELTE, 2023 tavasz

Fontos, hogy megfelelő kóddal vedd fel a tárgyat:

 * BSc: IP-18KVSZTME
 * MSc: IPM-18sztKVTEE
 * MSc esti: IPM-18EsztKVTEE

Előadás oktatója: Kaposi Ambrus (akaposi kukac inf.elte.hu).

Gyakorlatok oktatói (a 4-es csoportba csak eötvös kollégisták mehetnek):

| kurzus kód     | időpont               | helyszín                 | gyakorlatvezető név | ______@inf.elte.hu |
|----------------|-----------------------|--------------------------|---------------------|--------------------|
| 1              | Szerda 17:45-19:15    | Északi Tömb 7.16 (PC 12) | Bense Viktor        | qils07             |
| 2              | Kedd 17:45-19:15      | Déli Tömb 00-411 (PC 7)  | Merth Borbála       | f6tnix             |
| 3              | Csütörtök 16:00-17:30 | Déli Tömb 2-709 (PC 9)   | Petes Márton        | tx0lwm             |
| 4 EC-s csoport | egyeztetés alatt      | egyeztetés alatt         | Csimma Viktor       | midffj             |
| 5              | Csütörtök 17:45-19:15 | Északi Tömb 7.16 (PC 12) | Merth Borbála       | f6tnix             |

Nagyon fontos, hogy azt a gyakorlatot vedd fel a Neptunban, amelyikbe ténylegesen jársz, mert a Canvas automatikusan veszi át az infót a Neptunból.

Létezik egy [Típuselmélet 2023 tavasz](https://teams.microsoft.com/l/team/19%3ayjbZGERT-taiD-d93LrHeYsVpnjz3yCsIPRn-b2B7RE1%40thread.tacv2/conversations?groupId=8959a9ae-5b08-4acf-9cd5-aa0d1341df0e&tenantId=0133bb48-f790-4560-a64d-ac46a472fbbc) MS Teams csoport, ahol érdemes a típuselméletről beszélgetni. Kérj meg egy gyakorlatvezetőt, hogy adjon hozzá!

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
| 7.5-8.249 | 4    |
| 8.25-     | 5    |

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
|    2 | λ-kalkulus es veges tipusok, Bool=⊤|⊤ mint alkalmazas             | finite type iso                  |
|      | 2.3. λ-calculus                                                   | Bool beepitettkent               |
|      | 2.4 combinatory logic                                             |                                  |
|      | 2.5 products, sums, finite types                                  |                                  |
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
|      | 5.5 arithmetic of types (Fin (m|n) ≅ Fin m ⊎ Fin n)               |                                  |
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
| TODO | klasszikus vs. konstruktiv logika (sqrt(2) irrac)                 |                                  |
|      | parametricitas, Reynolds fabula                                   |                                  |
|      |                                                                   | f:Bool→Bool-ra f∘f∘f=f           |
|      | ellenpelda relaciok                                               | ellenpelda relaciok, fuggvenyek  |
|      |                                                                   | pigeonhole principle             |
|      | delay monad                                                       | delay monad                      |
