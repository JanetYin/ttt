{-
Informális bevezetés lesz a típuselméletbe, használjuk az Agda programozási nyelvet -- félév vége felé már precízen ki fogjuk tudni mondani, hogy mi az a lambda kalkulus

- korábban: Csörnyei Zoltán lambda kalkulusról szóló könyve
  - formális, de alacsony szintű matematikai leírása


típuselmélet
lambda kalkulus
Agda

egy programozási nyelv: Martin-Löf típuselmélet, implementációi pl. Agda, Coq, Idris, Lean
lambda kalkulus ennek a része

nyugodtan kérdezzetek akármikor, nem kell jelentkezni

mi az, hogy programozási nyelv? nehéz kérdés, de nem extra bonyolult. mi az, hogy Martin-Löf típuselmélet.


(3,1)  ~  2
(4,2)  ~  2
(1,4)  ~ -3
(2,5)  ~ -3

egész számok: ℕ × ℕ = {(a,b) | a∈ℕ, b∈ℕ}
              a-b =     a'-b'  → (a,b) = (a',b') 
              3-1 = 2 = 4-2    → (3,1) = (4,2)
              a+b' = a'+b      → (a,b) = (a',b')

zero : ℤ           0 típusa egész szám
suc  : ℤ → ℤ       suc egy művelet/program/függvény, input:egész szám, output:ℤ
pred : ℤ → ℤ
minden n-re pred(suc n)=n
minden n-re suc(pred n)=n
0 := zero
1 := suc(zero)
2 := suc(suc(zero))
3 := suc(suc(suc(zero)))
...
-1 := pred zero
-2 := pred (pred zero)
...
zero = pred (suc zero)

egész számok a szabad Abel-csoport az egyelemű halmazon (diszkrét matek)

jó lenne laptopot hozni, és az Agdát feltelepíteni rá
én is csinálok Agda live coding-ot

tematika: Thorsten Altenkirch könyve (Tao of types): http://www.cs.nott.ac.uk/~psztxa/mgs.2021/

nagyjából ez alapján haladunk

aSzámonkérés: előadást tart mindenki, jövő utáni héttől lehet
elmaradt az első két óra, jövő héten élőben lesz. 10-ig tart.

Emacs <- ebben él az Agda
vi

Tematika:

2. egyszerű típusok
3. ítéletlogika (nulladrendű logika)
4. adattípusok (induktív és koinduktív típusok)
5. függő típusok
6. elsőrendű logika (predikátumkalkulus)

matematika hagyományos felépítése: 
- elsőrendű logika (nyelv)
- Zermelo-Fraenkel halmazelmélet axiómával

alternatív:
- típuselmélet (kezdemények: Alonzo Church 1930-as évek, nagy lépés: 1972 Per Martin-Löf, 2006 körül: Vladimir Voevodsky)
  - nincs külön logikai nyelv meg halmazelmélet, hanem egyben
  - sokkal egyszerűbb, filozófiailag megalapozottabb
  - programozási nyelv, számítógépen végrehajthatók a bizonyítások
  - típusok: Python (halmazelmélet) <-> Java (típuselmélet)
             futási időben derül ki a hiba <-> mielőtt lefuttatod a programot
    -> "megkülönböztethetetlen dolgok egyenlők lehetnek"
    halmazelméletben ({0,1} = {3,4}) hamis
    típuselméletben bármely kételemű halmaz egyenlő (lehet)
    - absztrakt matematika formalizálható
  - számítógépes bizonyító rendszerek (proof assistant): matematikai bizonyításokat számítógéppel lehet ellenőrizni

(Gödel tétel)
-}

-- egyszeru tipusok

-- termeszetes szamok (nem kell erteni)
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

-- file megnyitas: C-x C-f
-- buffer bezaras: C-x k
-- terulet kijelelosenek kezdete: C-space
-- ha vegeztel a terulet kijelolesevel: C-w vagy M-w
-- UNDO: C-g C-g C-g
-- yank (paste): C-y

-- find file: C-x C-f
-- buffer bezaras: C-x k
-- terulet kijelelosenek kezdete: C-space
-- ha vegeztel a terulet kijelolesevel: C-w vagy M-w
-- UNDO: C-g C-g C-g
-- C-x 0 az aktualis ablakot bezarja
-- C-x 1 csak az aktualis ablakot hagyja meg
-- C-x 2 ketteosztas, egyik fajta
-- C-x 3 ketteosztas, masik fajta
-- navigacio: C-f  M-f  forwards
-- navigacio: C-b  M-b   backwards
-- navigacio: C-p        previous line
-- navigacio: C-n        next line

-- killer feature: rectangle edit
-- C-x r k        rectangular cut
-- C-x r y        rectangular yank

-- Agda parancs C-c C-l
-- Agda input mode be/ki: C-\
-- ha van Agda input mode: \bN   ℕ    \Ga  alpha  \GA  nagybetus alpha     α  Α    Γ γ
-- lyukban: info a lyukrol: C-c C-,
--          ha beleirtal valamit a lyukba, akkor info a lyukrol: C-c C-.
--          lyuk tartalmanak elfogadasa (lyuk megszuntetese): C-c C-space
-- C-c C-n  normalizalas

-- fuggvenyek:

f : ℕ → ℕ  -- f bemenete termeszetes szam, kimenete is
f x = x + 2
{-
f fekete doboz

        f
      -------
10--->|     |--->12
      -------
-}

-- C-c C-n    (f 10)  <- függvény alkalmazás       f(10) helyett f 10

f' : ℕ → ℕ
f' = (λ x → x + 2)   -- nevtelen fuggveny

--   rövidítés   matek
-- f 10 = 10 + 2 = 12
-- (λ x → x + 2) 10 = (x + 2)[x := 10] = 10 + 2 = 12
--              β redukció
-- (λ x → t) u = t[x := u] = t-ben x összes előfordulását u-ra helyettesítem
-- t akármi lehet, tartalmazhatja az x-et
-- u is akármi lehet
{-

        add      add 10
      -------    -----
10--->|     |--->|   |
      -------    ----

      add 10
      ------
  3-->|    |---> 13
      ------

-}

-- add : ℕ → (ℕ → ℕ)
add : ℕ → ℕ → ℕ        -- A → B → C = A → (B → C)  -- (ℕ × ℕ → ℕ)
                                                   -- int add(int x, int y)
-- add x = λ y → x + y
-- add x y = x + y
-- add = λ x → (λ y → x + y)  
add = λ x y → x + y    -- λ x y → t = λ x → (λ y → t)
                       -- f a b = (f a) b
-- curry-zés  (Haskell Curry, Alonzo Church tanítványa volt)

k : (ℕ → ℕ) → ℕ       -- magasabbrendu fuggveny
k h = h 2 + h 3

{-
         h        k
      -------    -----
      |     |--->|   |--> 0
      -------    ----
-}

-- k f = f 2 + f 3 = (2 + 2) + (3 + 2) = 9
-- k f = (λ h → h 2 + h 3) (λ x → x + 2) =
--    (h 2 + h 3)[h := (λ x → x + 2)] =        -- (λ x → t) u = t[x := u]
--    (λ x → x + 2) 2 + (λ x → x + 2) 3 =     
--           \___/ \_/
--             t    u
--     (x+2)[x:=2]    + (x+2)[x:=3] = (2+2)+(3+2) = 9

-- milyen tipusaink vannak? ℕ, (ℕ → ℕ), ℕ → (ℕ → ℕ), (ℕ → ℕ) → ℕ

variable
  A B C : Set

id : A → A        -- id :: a -> a
id x = x

_∘_ : (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

-- (f ∘ (add 3)) 4 = ((λ x → x + 2) ∘ add 3) 4 =
-- (λ x → x + 2) ((add 3) 4) =
-- add 3 4 + 2 = (3 + 4) + 2 = 7 + 2 = 9

ketszer : (A → A) → A → A
ketszer = λ f a → f (f a)

-- ketszer f 10 = f (f 10) = (10 + 2) + 2 = 14

-- : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ)
--    ^
--    |         =A       =A
--    |      /-----\   /----\
--    |    : (ℕ → ℕ) → ℕ → ℕ
-- /-----\ /-----\
-- ketszer ketszer (add 3) 1 =
-- (ketszer ketszer) (add 3) 1 =
-- ((λ f a → f (f a)) ketszer) (add 3) 1 =
-- (λ a → ketszer (ketszer a)) (add 3) 1 =
-- "negyszer (add 3) 1" =
-- add 3 (add 3 (add 3 (add 3 1))) =
-- 3*4+1 = 13

-- Agda + Emacs
-- apt-get install agda emacs

negyszer negyszer' : (B → B) → B → B
negyszer = ketszer ketszer
{-                 \_____/
                   : (B → B) → B → B
           \_____/
           ((B → B) → (B → B)) → (B → B) → (B → B)
-}
{-

            f       ∘ g

       g : A₁ → A₂
       f : A₂ → A₃
       A₁ = A₂ = A₃ = B → B
-}

+2 = f

negyszer' = ketszer ∘ ketszer
{-                    \_____/
                     : (B → B) → B → B
           \_____/
           (B → B) → (B → B)


negyszer +2 0 =
ketszer ketszer +2 0 =
(λ f a → f (f a)) ketszer +2 0 =              (λ x → t) u = t[x := u]
(λ a → ketszer (ketszer a)) +2 0 =
(ketszer (ketszer +2)) 0 =
(ketszer ((λ f a → f (f a)) +2)) 0 =
(ketszer (λ a → +2 (+2 a))) 0 =

               app
              /  \
            app   0
            / \                     abstract syntax tree
      ketszer  λa
                |


1+(2*3)

      f x
       |
       ;
      / \
printf   return
  |         |                           cons
"hello"     +                 "hello" = /  \
           / \                         'h'  cons
          x  *                               /  \
             /\                             'e'  cons
            1  x                                   ....


int f(int x) {            int f(int z) {     
  printf("hello");          printf("hello"); 
  return (x+(1*x))    =     return (z+(1*z)) 
}                         }                  

 100     100       100   
  Σ x =   Σ y =     Σ i
 x=1     y=1       i=1

 10^10                  10^10           
  Σ  sqrt(x)-x^3   =     Σ  sqrt(y)-y^3 
 x=0                    y=0             

 100     100      
  Σ v0 =  Σ v0
  1       1

 10    2                10    2         
  Σ  ( Σ   i+j)    =     Σ  ( Σ v1+v0)  
 i=0   j=1               0    1       


  10
  ∫  
 x=1

  d(◼²+◼*y³+2)
  ---------------- = (x ↦ 2x+y³)  = f , ahol f(x)=2x+y³
      d■           

negyszer' +2 0 =


De Bruijn indexek (Automath)

(λ x → x)                     λ v0      
(λ x → (λ y → x))             λ (λ v1)
(λ x → (λ y → y))             λ (λ v0)
(λ x → (λ y → x + (y + 3)))   λ (λ (v1 + (v0 + 3)))

(λ x → (λ x → x))             λ (λ 0)

void f(int x) {
  g(3);
  void g(int x) {
    print(x);
    // nem tudom kiirni a kulso x-et!!
  }
}

f(2);

λ y → (λ x → (λ y → x+y)) y = (λ y → x+y)[x ↦ y] =        (λ y → y + y)
(λ x → (λ y → x+y)) y = (λ z → (λ q → z+q)) y = (λ q → y+q) = (λ q → y+q)
-}

f∘g : ℕ
f∘g = 3

-- kompozicio nem kommutativ

f1 f2 : ℕ → ℕ
f1 = λ x → x + x
f2 = λ x → x + 1
{-
8 =(matek)
4 + 4 =(helyettesites)
(x + x)[x↦ 4] =(β-redukcio)
(λ x → x + x) 4 =(matek)
(λ x → x + x) (3 + 1) =(helyettesites)
(λ x → x + x) ((x + 1)[x↦3]) =(β-redukcio)
(λ x → x + x) ((λ x → x + 1) 3)   =(f1, f2 def.)
f1 (f2 3) =(_∘_ def)
(f1 ∘ f2) 3 =(f1 ∘ f2 = f2 ∘ f1)
(f2 ∘ f1) 3 =(_∘_ def)
f2 (f1 3) =(f1, f2 def)
(λ x → x + 1) ((λ x → x + x) 3) =(β-redukcio)
(λ x → x + 1) ((x + x)[x↦3]) =(helyettesites)
(λ x → x + 1) (3 + 3) =(alt.isk.matek)
(λ x → x + 1) 6 =(β-redukcio)
(x + 1)[x↦6] =(helyettesites)
6 + 1 =(alt.isk.matek)
7
-}

-- TODO: belatni Agdaban is majd ha eljutunk odaig

-- lambda kalkulus, β, kötés, η

K : A → (B → A)           --  k :: a -> b -> a   A k<A,B>(A a, B a) { return a; }
K = λ a → λ b → a

S : (A → B → C) → (A → B) → A → C
S = λ f → λ g → λ a → f a (g a)   -- (g a) : B

I : A → A
I = S K (K{_}{ℕ}) -- ne hasznalj λ-t, csak S-t es K-t!

-- S K K = ( λ f → λ g → λ a → f a (g a)) (λ a b → a) (λ a b → a) =(HF) ... = λ a → a

-- S{A}{B}{C} : (A → B → C) → (A → B) → A → C
-- K{A}{B} : (A → B → A)
-- S{A}{A→A}{A} (K{A}{A→A}) (K{A}{A})  : A → A
-- S{A}{B→A}{A} : (A → (B→A) → A) → (A → (B → A)) → A → A
-- S{A}{B→A}{A} (K{A}{B→A}) (K{A}{B}) : A → A
-- K{A}{B} : (A → B → A)

-- λ x → M konvertalasa SK kifejezesre, M-ben lehet S,K,applikacio,valtozo, de nincs benne λ
-- (1) λ x → x ~~> I
-- (2) λ x → y ~~> K y
-- (3) λ x → M₁ M₂ ~~> S (λ x → M₁) (λ x → M₂)
--     \_________/       \_______/  \________/
--       : A → C         :A → B → C  :A → B
--                     \_____________________/
--                        : A → C
--      x : A ,  M₁ : B → C,  M₂ : B,   M₁ M₂ : C
-- (4) λ x → K   ~~>  K K
-- (5) λ x → S   ~~>  K S


U : A → B → B
-- U = λ x y → y -- ne hasznalj λ-t, csak S-t es K-t!
U = S (S (K S) (K K)) (K (K {_}{ℕ}))

_∘'_ : (B → C) → (A → B) → (A → C)
_∘'_ = λ f g a → f (g a) -- hasznald a konverzios algoritmust!

-- igaz-e, hogy _∘_ = _∘'_ ?

swap : A → (A → B) → B
swap = λ a f → f a -- hasznald a konverzios algoritmust!

flip : (A → A → B) → A → A → B
flip = λ f a a' → f a' a -- hasznald a konverzios algoritmust!

-- eddig HF

-- haromelemu tipus

data Three : Set where
  zero one two : Three

-- FEL: C-c C-d -vel nezd meg, mi a tipusa zero-nak, one-nak es two-nak

-- osszeg tipus

data _⊎_ (A B : Set) : Set where -- \u+
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- FEL: hany eleme van Three ⊎ Three -nek? es Three ∪ Three -nek? (utobbit Agdaban nem tudjuk leirni)

-- FEL: add meg Three ⊎ Three osszes lehetseges elemet! ha tobb van, mint 4, meg vegyel hozza ujabbakat!
t1 t2 t3 t4 : Three ⊎ Three
t1 = {!!}
t2 = {!!}
t3 = {!!}
t4 = {!!}

-- FEL: nyomj C-c C-c -t a lyukban. ezt hivjak automatikus mintaillesztesnek (pattern matching)
case : (A → C) → (B → C) → A ⊎ B → C
case f g w = {!w!}

-- FEL: hany eleme van ℕ ⊎ ℕ -nak?

-- FEL: minek van tobb eleme? ℕ -nek vagy ℕ ⊎ ℕ -nek?

-- szorzat tipus (record)

record _×_ (A B : Set) : Set where -- \times
  field
    proj₁ : A
    proj₂ : B
open _×_ public

-- FEL: nezd meg C-c C-d -vel, hogy mi a proj₁ es a proj₂ tipusa!

-- FEL: menj be a lyukba, es nyomj C-c C-c -t! ezt hivjak ko-mintaillesztesnek. utana toltsd be a lyukakat!
_,_ : A → B → A × B
a , b = {!!}

-- ez mindig teljesul Agdaban (surjective pairing, η a szorzat tipusra): (proj₁ w , proj₂ w) = w

-- FEL
curry : (A × B → C) → A → B → C
curry = {!!}

-- FEL
uncurry : (A → B → C) → A × B → C
uncurry = {!!}

-- FEL: mutasd meg egyenlosegi ervelessel, hogy curry (uncurry f) = f

-- FEL: mutasd meg egyenlosegi ervelessel, hogy uncurry (curry g) = g

-- FEL: add meg Three × Three osszes lehetseges elemet! ha tobb van, mint 4, meg vegyel hozza ujabbakat!
r1 r2 r3 r4 : Three × Three
r1 = {!!}
r2 = {!!}
r3 = {!!}
r4 = {!!}

-- FEL
uncase : (A ⊎ B → C) → (A → C) × (B → C)
uncase = {!!}

-- FEL: csak case-t hasznald, ne hasznalj mintaillesztest!
case'  : (A → C) × (B → C) → A ⊎ B → C
case' = {!!}

-- FEL: mutasd meg egyenlosegi ervelessel, hogy uncase (case' f) = f

-- FEL: probald meg megmutatni egyenlosegi ervelessel, hogy case' (uncase g) = g

-- egyelemu tipus

record ⊤ : Set where -- \top

-- FEL: hasznalj ko-mintaillesztest!
tt : ⊤
tt = {!!}

-- ures tipus

data ⊥ : Set where -- \bot

-- FEL: hasznalj mintaillesztest!
case⊥ : ⊥ → A
case⊥ = {!!}

-- veges tipusok, fuggvenyek kozottuk

-- FEL: adj meg egy 4-elemu tipust (data nelkul)!
Four : Set
Four = {!!}

-- FEL: add meg mind a negy elemet!
four0 four1 four2 four3 : Four
four0 = {!!}
four1 = {!!}
four2 = {!!}
four3 = {!!}

-- FEL: adj meg harom masik 4-elemu tipust (data nelkul), melyek nem egyenloek Four-ral!
Four' Four'' Four''' : Set
Four' = {!!}
Four'' = {!!}
Four''' = {!!}

-- FEL: adj meg egy negyelemu tipust data-val!

-- FEL
A× : (B → C) → A × B → A × C
A× = {!!}

-- FEL: bizonyitsd be egyenlosegi ervelessel, hogy A× id = id

-- FEL: bizonyitsd be egyenlosegi ervelessel, hogy A× (f ∘ g)=(A × f) ∘ (A × g)

-- ezzel befejeztuk http://www.cs.nott.ac.uk/~psztxa/mgs.2021/simple-types.pdf -t
