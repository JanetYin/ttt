Lemmák:
reflℕ   ∀ a ∈ ℕ :                                   a = a
transpℕ ∀ a , b ∈ ℕ , P ∈ (ℕ ↦ 𝕃) : a = b →         P(a) = P(b)
sym     ∀ a , b ∈ ℕ :               a = b →         b = a
trans   ∀ a , b , c ∈ ℕ :           a = b ∧ b = c → a = c
cong    ∀ f ∈ (ℕ ↦ ℕ) , a , b ∈ ℕ : a = b →         f(a) = f(b)
disj    ∀ a ∈ ℕ :                                   ¬(0 = a + 1)
inj     ∀ a , b ∈ ℕ :                               a + 1 = b + 1
idl     ∀ a ∈ ℕ :                                   0 + a = a
idr     ∀ a ∈ ℕ :                                   a + 0 = a
ass     ∀ a , b , c ∈ ℕ :                           (a + b) + c = a + (b + c)
suc+    ∀ a , b , c ∈ ℕ :                           (1 + a) + b = a + (1 + b)
comm    ∀ a , b ∈ ℕ :                               a + b = b + a
idl*    ∀ a ∈ ℕ :                                   1 * a = a
idr*    ∀ a ∈ ℕ :                                   a * 1 = a
nulll   ∀ a ∈ ℕ :                                   0 * a = 0
nullr   ∀ a ∈ ℕ :                                   a * 0 = 0
distr   ∀ a , b , c ∈ ℕ :                           (a + b) * c = a * c + b * c
ass*    ∀ a , b , c ∈ ℕ :                           (a * b) * c = a * (b * c)
suc*    ∀ a , b ∈ ℕ :                               a + a * b = a * (1 + b)
comm*   ∀ a , b ∈ ℕ :                               a * b = b * a
distl   ∀ a , b , c ∈ ℕ :                           a * (b + c) = a * b + a * c

Összeadás definíciója: \( a + b \) az a szám, ami b-nek az annyiszor vett rákövetkezője, ahányszor kell venni a 0 rákövetkezőjét, hogy \( a \)-hoz jussunk.
Összeadás axiómái, definíciója alapján:
    ∀ a ∈ ℕ :       0 + a = a
    ∀ a , b ∈ ℕ :   (1 + a) + b = 1 + (a + b)
                    0 = 0
    1 + 0 = 1 , 1 + 1 = 2 , 1 + 2 = 3 , 1 + 3 = 4 , …

Szorzás definíciója: a * b = fᵃ(0) ahol f(x) = b + x
Szorzás axiómái, definíciója alapján:
    ∀ b ∈ ℕ :       0 * b = 0
    ∀ a ∈ ℕ :       (1 + a) * b = b + a * b

Egyéb függvények:
pred'(x) : ℕ ↦ ℕ ⊎ ⊤        Az x előtti szám, vagy ha x = 0 akkor tt
eq0(x) : ℕ ↦ Bool           x = 0
eqℕ(x , y) : ℕ × ℕ ↦ Bool   x = y
Eqℕ(x , y) : ℕ × ℕ → 𝕃      x = y
A ◾ B {x} {y} {z} ∈ 𝕃      x = z (A ∈ x = y , B ∈ y = z)
