{-
Tipuselmelet, típuselmélet, type theory
- type theory ≠ study of type systems of progr.lang.s
- type theory = Martin-Löf's type theory = as it is implemented by Agda

Kaposi Ambrus
Dept. of Prog.Langs. and Compilers
16:00-17.30  exactly
- you can stop me any time and ask questions / comments

website: google my name, website, teaching/tipuselmelet
bitbucket.org/akaposi/ttt

requirements:
- tutorial: micro-zh -- small Agda program, 0/1 points
  homework after tutorial, preparing for the micro-exam
- for each lecture, canvas quiz
- exam in the exam period, on computer, example exam on the website, 2 hours
  - prerequisite: tutorial >1 grade, canvas quiz >50%

technical requirements: git, Agda (with Emacs), (Linux, NixOS)

-}

open import Lib

{-
Curry-Howard isomorphism
category (McLane and ...)
ZF -- Zermelo-Fraenkel set theory

mathematics is built on first-order logic and
  the axioms of ZF set theory

type theory is alternative foundation of mathematics
  instead of f.o.l. and set theory

- set theory    python    dynamic   2 ∈ ℕ proposition
  type theory   java      static    2 : ℕ static information
- type theory is high level:
  Zermelo: 0 := {}, 1 := {{}}, 2 := {{{}}}, ...
  Neumann: 0 := {}, 1 := {{}}, 2 := {{}, {{}}}, 3 := {0, 1, 2}, 
  2 ∈ 4 for Neumann, but not Zermelo
- Cantor: let's design a theory for collections
  - we build collections using predicates = { x | s.t. x + 2 > 3 }, { x | x ∌ x }
  - in type theory, the notion of predicate comes after collection

Haskell Curry, PhD student Alonzo Church (lambda calculus)  (λ x → add(x)(2))
combinatory logic by Moses Schönfinkel, SK combinators

-- currying:  instead of (A × B → C) you write (A → (B → C))
--                       _+_ : ℕ → (ℕ → ℕ)
--                       3+_ :      ℕ → ℕ

mathematicians use t.t. to computer check their proofs
programmers use t.t. to computer check their programs

addition : ℕ → ℕ → ℕ
addition x y | x == 34972578642958275 && y == 8325702495809485 = 42
             | otherwise = x + y

implementations (proof assistants):
Agda   SWEDISH  very similar to Haskell, mainly for type theorists, most features
Coq    FRENCH   very practical, Chrome, Firefox, Linux kernel  (formal semantics)
Lean   AMERICAN mathematicians use this, formalisation
Idris  SCOTTISH very similar to Haskell, programming

related courses = discrete mathematics (algebra), logic, computability, formal languages, compilers, Haskell/Clean
-}

-- : instead of ::

add2 : ℕ → ℕ   -- \bN
add2 x = x + 2
-- f x instead of f(x)
-- f (1 + 2) instead of f(1+2)

plus : ℕ → ℕ → ℕ
plus x y = x + y

k : (ℕ → ℕ) → ℕ
k h = h 2 + h 3

-- running a program:
-- k add2 = add2 2 + add2 3 = (2 + 2) + (3 + 2) = 4 + 5 = 9

add2' : ℕ → ℕ   -- \bN
add2' = (λ x → x + 2)

-- k (λ x → 3 * x + 1) = ... = 17

