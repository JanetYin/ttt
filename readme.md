# Type theory (Agda) course, Hungarian name: típuselmélet, ELTE, Spring 2024

Important that you register the course with the code appropriate to your studies:

 * BSc: IP-18KVSZTM[E|G]
 * MSc: IPM-18sztKVTE[E|G]
 * MSc evening course: IPM-18EsztKVTE[E|G]

Lectures are given by Ambrus Kaposi (akaposi at inf.elte.hu). THIS SEMESTER THE LECTURES ARE IN ENGLISH!

Teachers of tutorials:

| course code    | time            | place                                | teacher             | ______@inf.elte.hu | Language |
|----------------|-----------------|--------------------------------------|---------------------|--------------------|----------|
| 1              | Wed 17:45-19:15 | South Building 2-124 (Microsoft Lab) | Viktor Bense        | qils07             | HU       |
| 2              | Tue 17:45-19:15 | South Building 00-411 (PC7)          | Borbála Merth       | f6tnix             | HU       |
| 3              | Thu 16:00-17:30 | South Building 00-503 (PC8)          | Bálint Bence Török  | fcjylp             | HU       |
| 4              | Thu 17:45-19:15 | South Building 2-124 (Microsoft Lab) | Márton Petes        | tx0lwm             | EN       |

It is very important that your tutorial registered in Neptun is the same where you physically go to because Canvas obtains information automatically from Neptun.

There is a MS Teams team called "Típuselmélet 2024 tavasz" where you can discuss about type theory. You can join using the code wbgq7ec. We recommend asking questions here instead of writing emails to the teachers. You will get an answer faster, and others can learn from your question as well.

Requirements:

 * Canvas quiz for each lecture.
 * Small Agda exercise "micro-zh" at the beginning of each tutorial. Homeworks help preparing for these.
 * Computer exam in the exam period. [Example exam](https://bitbucket.org/akaposi/ttt/raw/master/2022aut/exampleExam.agda)

The tutorial grade is calculated from the micro-zhs which are all worth 0 or 1 points. Point limits:

| points    | grade |
|-----------|-------|
| 0-4.999   | 1     |
| 5-6.249   | 2     |
| 6.25-7.49 | 3     |
| 7.5-8.749 | 4     |
| 8.75-     | 5     |

Only those are allowed to enter the exam whose average Canvas quiz result is above 50% and who obtained a >1 grade at the tutorial.

Compulsory literature:

 * [Thorsten Altenkirch. Tao of types](http://www.cs.nott.ac.uk/~psztxa/mgs.2021)

Recommended literature:

 * [Homotopy Type Theory book](http://saunders.phil.cmu.edu/book/hott-online.pdf) (especially Chapter 1 Type theory)
 * [Egbert Rijke. Introduction to homotopy type theory](https://arxiv.org/pdf/2212.11082)
 * [Daniel P. Friedman and David Thrane Christiansen. The little typer](https://thelittletyper.com)
 * [Edwin Brady. Type-driven development with Idris](https://www.manning.com/books/type-driven-development-with-idris)
 * [Kaposi Ambrus. Bevezetés a homotópia-típuselméletbe](https://akaposi.github.io/hott_bevezeto.pdf) (magyar)
 * [Martin Hofmann. Syntax and Semantics of Dependent Types](https://www.tcs.ifi.lmu.de/mitarbeiter/martin-hofmann/pdfs/syntaxandsemanticsof-dependenttypes.pdf)
 * [Ambrus Kaposi. Type systems course notes](https://bitbucket.org/akaposi/typesystems/raw/master/src/main.pdf)

## Preliminary schedule

See the Section numbers of the Tao book below.

| week | lecture                                                           | tutorial                                 |
|------|-------------------------------------------------------------------|------------------------------------------|
|    1 | intro, functions (examples with built-in ℕ)                       | Emacs and Agda usage,                    |
|      | 2.2. identity, composition, polymorphism                          | simple fcts on built-in ℕ                |
|    2 | λ calculus and finite types, Bool=⊤+⊤ as an application           | finite type iso                          |
|      | 2.3. λ-calculus                                                   | built-in Bool                            |
|      | 2.4 combinatory logic                                             |                                          |
|      | 2.5 products, sums, finite types                                  |                                          |
|      | derivation of typing using derivation rules                       |                                          |
|    3 | inductive types using data, Bool                                  | inductive types                          |
|      | 4.1-4.2 inductive types: Nat, Maybe, Ackermann, iterator-recursor |                                          |
|      | 4.3 List, Expr, RoseTree, (Ord)                                   |                                          |
|    4 | which inductive defs are valid, coinductive types                 | positivity, coinductive types            |
|      | 4.4 positivity, Λ                                                 |                                          |
|      | 4.5 coinductive types: stream, conat                              |                                          |
|      | (4.6 functorial semantics)                                        |                                          |
|    5 | dependent types                                                   | vec, fin                                 |
|      | 5.1 Vec                                                           |                                          |
|      | 5.2 Fin, Vec indexing                                             |                                          |
|      | 5.3 Π es Σ                                                        |                                          |
|    6 | dependent types                                                   | fin                                      |
|      | 5.4 relating simple and dependent type formers                    |                                          |
|      | 5.5 arithmetic of types `(Fin (m+n) ≅ Fin m ⊎ Fin n)`             |                                          |
|    7 | classical logic, predicates, relations, first-order logic         | propositional logic                      |
|      | 3.1 Boolean logic                                                 |                                          |
|      | 3.2 prop as types                                                 |                                          |
|      | 6.1 predicates and quantifiers                                    |                                          |
|    8 | predicates and relations                                          | predicate logic                          |
|      | 6.2 first order logical equivalences                              |                                          |
|      | 6.3 equality                                                      |                                          |
|    9 | induction on ℕ                                                    | properties of div,*                      |
|      | 6.4 properties of addition                                        |                                          |
|   10 | equational reasoning                                              | equational reasoning                     |
|   11 | more properties of inductive types: injectivity and disjointness  | data constructors injective and disjoint |
|      | of constructors, decidability of equality                         | decidable equality                       |
|      |                                                                   |                                          |
| TODO | classical vs. constructive logic (a,b irrational and a^b rational)|                                          |
|      | parametricity, fable by Reynolds                                  |                                          |
|      |                                                                   | f:Bool→Bool-ra f∘f∘f=f                   |
|      | relations which are counterexamples                               | counterexample rels and fcts             |
|      |                                                                   | pigeonhole principle                     |
|      | delay monad                                                       | delay monad                              |
|      | divisibility, if `d|x` and `d|y` then `d|x+y`                     |                                          |
|      | ⊤ ≠ ⊤ ⊎ ⊤                                                         |                                          |

## Introduction and elimination rules

| type  | intro (if this is the Goal) | elim (if we have an assumption called t)                     |
|-------|-----------------------------|--------------------------------------------------------------|
| ⊥     |                             | exfalso t                                                    |
| ⊤     | tt                          |                                                              |
| ⊎     | inl ?, inr ?                | case t ? ?, ind⊎ P ? ? t                                     |
| ×,Σ   | ? , ?                       | fst t, snd t                                                 |
| →     | λ x → ?                     | t ?                                                          |
|       |                             |                                                              |
| Bool  | true,false                  | if t then ? else ?, indBool P ? ? t                          |
| ℕ     | zero,suc                    | iteNat ? ? t, recNat ? ? t, indNat P ? ? t                   |
