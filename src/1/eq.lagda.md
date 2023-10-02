# Definicionális egyenlőségek

```
open import Lib
```

Vegyük az alábbi példát:

```

_∧₁_ : Bool → Bool → Bool
true ∧₁ true = true
_    ∧₁ _    = false

```

Mint láthatjuk, az előbbi példánál a sor elejét agda kiemeli, mert átfedés van az esetek között.

Nézzünk meg egy másik definíciót!

```

_∧₂_ : Bool → Bool → Bool
true ∧₂ b = b
false ∧₂ _ = false

```

Ebben az esetben nincsen kiemelve egyik sor se, tehát nincsen átfedés az eseteink között!

Mi a különbség a két definíció között?
Első ránézésre semmi, mindkettő pontosan ugyanúgy működik.
Azonban ha elkezdünk egy kicsit játszani a két éssel, rögtön kiderül,
hogy különbség nagyon is sok van közöttük, a két függvény teljesen másképp
működik, ebből következően teljesen másképp viselkedik.
Nézzünk példákat erre, hogy is látszódik ez meg.

```

∧₁-ex1 : true ∧₁ true ≡ true
∧₁-ex1 = refl

```

Ebben semmi meglepő nincs, maga ez a sor a definícióban is ott van.

```

∧₂-ex1 : true ∧₂ true ≡ true
∧₂-ex1 = refl

```
Definíció szerint az lesz az eredmény, amit a második paraméter helyére helyettesítek.

```

∧₁-ex2 : true ∧₁ false ≡ false
∧₁-ex2 = refl

∧₂-ex2 : true ∧₂ false ≡ false
∧₂-ex2 = refl

```

Amíg a két érték egyértelműen adott,
addig semmi különbséget nem fogunk tapasztalni.

Nézzünk egy érdekesebb esetet, ahol érdekességekkel tudunk találkozni.

```

∧₁-ex3 : (λ a → false ∧₁ a) ≡ (λ a → false)
∧₁-ex3 = refl

∧₂-ex3 : (λ a → false ∧₂ a) ≡ (λ a → false)
∧₂-ex3 = refl

```

Ez az eset még mindig jól működik, definíció szerint ha az első paraméter nem true, akkor az csak false lehet, és abban az esetben az eredmény false, tehát agda ekkor még tud normalizálni.

Az alábbi példában találkozunk az igazi érdekességgel.

```

∧₁-ex4 : (λ a → true ∧₁ a) ≡ (λ a → a)
∧₁-ex4 = {! refl !}

∧₂-ex4 : (λ a → true ∧₂ a) ≡ (λ a → a)
∧₂-ex4 = refl

```

Az ∧₁-es egyenlőség már nem fog teljesülni definíció szerint, mert a második paraméterről is egyértelműen tudni kell, hogy micsoda.
Ha megpróbáljuk az ∧₁-es egyenlőséget refl-lel bizonyítani, akkor fordítási hibát kapunk:
true ∧₁ a ≠ a of type Bool

> Az ∧₁-es egyenlőség bizonyíthatóan teljesül, de nem definíció szerint.

Az ∧₂-es egyenlőség ezzel szemben definíció szerint teljesülni fog, pont így van definiálva, csak az első paramétertől függ, hogy a függvény miként viselkedik.

**Éppen ezért érdemes a függvényeket megpróbálni úgy definiálni, hogy minél kevesebb paraméterre kelljen mintailleszteni, mert akkor több eset fog definíció szerint működni, amelynél agdában nincs jobb működés.**
