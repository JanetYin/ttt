# 1 gyakorlat

## Kód / Könyvtár megszerzése

1. git clone https://bitbucket.org/akaposi/ttt
2. Nyisd meg az így kapott mappát emacs/VSCode-ban.
3. Ellenőrizd a típust/töltsed be a fájlt "C-c C-l"
    - Most már színesnek kell lennie a fájlnak. :)

## Szükséges kombinációk

### Emacx

Emacs key bindings (C = Ctrl, M = Alt):
-  C-x C-f : create or open a file
-  C-x C-w : save (write) file
-  C-x C-c : close Emacs
-  C-space : start selecting text
-  M-w : Copy
-  C-w : Cut
-  C-y : Paste

### Visual Studio code

Agda-mode key bindings:
-  C-\       : Switch Agda input mode on/off
-  C-c C-l   : Typecheck the current file
-  C-c C-n   : Normalise an expression (reduce the expression as much as possible)
-  C-c C-d   : Deduce the type of an expression
-  C-c C-,   : Show the goal type and context of a hole
    - (C-u C-u C-c C-, : same but fully normalise the goal
    - C-u C-c C-,     : same but do not normalise the goal)
-  C-c C-.   : Goal type and context + inferred type of current expression
-  C-c C-SPC : Fill goal
-  C-c C-x = : Describe character at point

### Unicode

Unicode szimbólumok, amiket használunk:
- → ~ \to
   - \rightarrow
-    ℕ ~ \bN 
   -'b'lackboard 'N', és természetesen van \bZ a ℤ leírásához, stb
-  λ ~ \Gl 
   - 'G'reek 'l', és természetesen van \GG a Γ leírásához, stb

## TODAY:
- Az alap típus ℕ
   - Emlékeztető: A természetes számokat induktívan definiáljuk
      - `zero : ℕ` vagyis legyen egy szám, amit kijelölünk nullának
      - `suc n : ℕ → ℕ` vagyis legyen egy szám, ami egy rákövetkezője egy másik számnak. Legegyzserűbben ezt úgy lehet érteni, mintha +1-et hozzáadnék
         - zero = 0; suc zero = 1; suc (suc zero) = 2; suc (suc (suc ... )) = 42
         - Amennyu suc-ot látsz, anníi az értéke a számnak
- függvény típusok   A → B
   - Ahol is `A` és `B` Típusok 

## Kód

Emlékeztető:

### Modul és könyvtár

```agda

module gy01l where

open import Lib

```

Kulcs szavak:

- module <_name_> where : A modulunkat elnevezzük
   - Több modult is létre tudunk hozni
   - Egy fő modulunk van, aminek meg kell egyeznie a fájl nevével, és ezt kell mindig legelsőnek felírnunk.
- open <_module/type_> : A modult, vagy típust "kinyitja", vagyis tudjuk használni modul vagy típus specifikálás nélkül.
- import <_module-name_> : beimportálja a megelelő névvel rendelkeő modult.


### Függgvények és lyuk

```agda

add3 : ℕ → ℕ
add3 x = x + 3

🤙+ : ℕ
🤙+ = 10

```

függvény deklaráció: <_fv-név_> : <_fv-típus_>
függvény implementálása : <_fv-név_> <_paraméter(ek)_> = <_definíció_>

lyuk/hole: Agda itt tud normalizálni, behelyezni értékeket.
   - ? : "Ide még nem akarok írni", legtöbbször ezt írjuk le.
   - {! !} : A felkiáltójelek közé tudunk írni. Erre cseréli le agda a `?`-t.

try add3 x = x+3, spaces matter!

C-c C-n  add3 4

```agda

aNum : ℕ
aNum = add3 4

```

egyenlőségi érvelés
aNum = add3 4
      = 4 + 3
      = 7

nem kell írni zárójeleket "add3(4)"

C-c C-n aNum

```agda

bNum : ℕ
bNum = add3 (add3 (add3 2))

```

"add3 add3 add3 2" rossz kifejezés! Zárójelezés szükséges

C-c C-n bNum

### Lambda nótáció

```agda

add3' : ℕ → ℕ
add3' = λ x → x + 3
-- add3 x = x + 3

```

add3' 4 = (λ x → x + 3) 4
        = (x + 3)[x := 4]
        = (4 + 3)
        = 7

Próbáld ki C-c C-n beütésével!

```agda

add4 : ℕ → ℕ
add4 = _+ 4

```

Cél és kontextus:             C-c C-,
Cél, kontextus, és kiértékelt típus: C-c C-.
Lyukba helyezés                    : C-c C-space  ,  C-c C-r
Lyuk készítése: enter '?'

### Több paraméterrel rendelkező függvények

Definiáljuk az összeadást!

> Note:
> Ahogy feljebb említettem a `zero` és a `suc ?` is
> konstruktora a természetes számoknak, így tudunk
> arra mintát illeszteni!  
> Ha mintát illesztes a `suc` konstrulktor függvényre
> akkor kibontod belőle. Lényegét tekintve, olyan, mintha
> a számból kivontál volna belőle egyet.  
> Itt is működik a megkötéses (bind) mintaillesztés,
> vagyis hogy egyszerre több mintát is tudsz írni, ami
> a `@` jellel történik.  
> Ezt felhasználva legyen ez alábbi egy mintaillesztés:  
> ``` n@(suc m) ```  
> Ekkor mondhatjuk azt, hogy `n - 1 = m`.

```agda

add : ℕ → ℕ → ℕ
add x zero = x
add x n@(suc x₁) = suc (add x x₁)

```

```plaintext
ℕ → (ℕ → ℕ) = ℕ → ℕ → ℕ
            ≠ (ℕ → ℕ) → ℕ
```
`λ` zárójelezése

same as λ x → λ y → x + y  
same as λ x y → x + y

```agda

add3'' : ℕ → ℕ
add3'' = add 3

num1 : ℕ
num1 = add 3 4

-- zárójelezés applikáláskor

num1' : ℕ
num1' = (add 3) 4

```

Mi a gond a következővel?

```plaintext

num2 : ℕ
num2 = add (3 4)

```

Mi a gond a következővel?

```plaintext

num3 : ℕ
num3 = add 3 (add 4)

```

Számítsad ki egyenlőségi érveléssel:

```agda

num4 : ℕ
num4 = add 3 (add 4 2)

```

Magasabb-rendű függvények: függvények függvény paraméterrel
például Haskell-ben:   map :: (a -> b) -> [a] -> [b]

írj egy függvényt a következő típus szignatúrával:

```agda

f1 : (ℕ → ℕ) → ℕ
f1 x = x 5

```

Teszteld `f1 add3` és `f1 add4`-al!. Ugyanaz a végeredmény?

Írj két különböző függvényt, ami **használja** a paramétereit, hgy teljesüljön rá:
f2 add3 ≠ f2 add4 ≠ f3 add4 ≠ f3 add3

```agda

f2 f3 : (ℕ → ℕ) → ℕ
f2 _ = 5
f3 x = x (suc 68)

tw : {A : Set} → (A → A) → A → A
tw f n = f (f n)

-- Figyeld meg a következőt

t = tw tw add3 1

```

Mi a típusa neki, és miért? Kérdezd meg agdát (C-c C-d).
Mi az értéke? kérdezd meg agdát (C-c C-n).


```agda

first : {A : Set} → A → A → A
first x x₁ = x

second : {A : Set} → A → A → A
second x x₁ = x₁

```
