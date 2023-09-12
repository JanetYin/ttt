# 1 gyakorlat

## Kód / Könyvtár megszerzése

1. git clone https://bitbucket.org/akaposi/ttt
2. Open this file (PATH) in emacs/VSCode.
3. Typecheck with "C-c C-l"
    - The file should now be colored

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

List of unicode symbols:
- → ~ \to
   - \rightarrow
-    ℕ ~ \bN 
   -'b'lackboard 'N', there is also \bZ for ℤ, etc
-  λ ~ \Gl 
   - 'G'reek 'l', there is also \GG for Γ, etc

## TODAY:
- base type ℕ
- function types   A → B
   - where A and B are any types

## Kód

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

equational reasoning
aNum = add3 4
      = 4 + 3
      = 7

no need to write brackets in "add3(4)"

C-c C-n aNum

```agda

bNum : ℕ
bNum = add3 (add3 (add3 2))

```

"add3 add3 add3 2" is wrong

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

test it with C-c C-n!

```agda

add4 : ℕ → ℕ
add4 = _+ 4

```

Goal type and context:             C-c C-,
Goal type, context, inferred type: C-c C-.
Fill the hole                    : C-c C-space  ,  C-c C-r
Creating a hole: enter '?'

### Több paraméterrel rendelkező függvények

```agda

add : ℕ → ℕ → ℕ
add x zero = x
add x n@(suc x₁) = suc (add x x₁)

```

ℕ → (ℕ → ℕ) = ℕ → ℕ → ℕ
            ≠ (ℕ → ℕ) → ℕ
bracketing of λ

same as λ x → λ y → x + y
same as λ x y → x + y

```agda

add3'' : ℕ → ℕ
add3'' = add 3

num1 : ℕ
num1 = add 3 4

-- bracketing of application

num1' : ℕ
num1' = (add 3) 4

```

what is wrong with the following?

```plaintext

num2 : ℕ
num2 = add (3 4)

```

what is wrong with the following?

```plaintext

num3 : ℕ
num3 = add 3 (add 4)

```

compute with equational reasoning:

```agda

num4 : ℕ
num4 = add 3 (add 4 2)

```

Higher-order functions: functions with functions as arguments
e.g. in Haskell:   map :: (a -> b) -> [a] -> [b]

write a function of the following type:

```agda

f1 : (ℕ → ℕ) → ℕ
f1 x = x 5

```

test it with f1 add3, f1 add4. is the result the same?

write two different functions which use their inputs, i.e.
f2 add3 ≠ f2 add4 ≠ f3 add4 ≠ f3 add3

```agda

f2 f3 : (ℕ → ℕ) → ℕ
f2 _ = 5
f3 x = x (suc 68)

tw : {A : Set} → (A → A) → A → A
tw f n = f (f n)

-- consider

t = tw tw add3 1

```

what is the type of this and why? ask Agda too (C-c C-d).
what is its value?  guess, and ask Agda too (C-c C-n).


```agda

first : {A : Set} → A → A → A
first x x₁ = x

second : {A : Set} → A → A → A
second x x₁ = x₁

```
