Lemmák:
reflb   ∀ b ∈ Bool :                                            b = b
transpb ∀ (P : Bool ↦ 𝕃) , a , b ∈ Bool :       a = b ∧ P(a) →  P(b)
symb    ∀ a , b :                               a = b →         b = a
transb  ∀ a , b , c ∈ Bool                      a = b ∧ b = c → a = c
congb   ∀ (f : Bool ↦ Bool) , a , b ∈ Bool :    a = b →         f(a) = f(b)
disjb                                                           ¬ (true = false)
idl∧    ∀ a ∈ Bool :                                            true ∧ a = a
idr∧    ∀ a ∈ Bool :                                            a ∧ true = a
ass∧    ∀ a , b , c ∈ Bool :                                    (a ∧ b) ∧ c = a ∧ (b ∧ c)
comm∧   ∀ a , b ∈ Bool :                                        a ∧ b = b ∧ a
null∧   ∀ a ∈ Bool :                                            false ∧ a = false
idl∨    ∀ a ∈ Bool :                                            false ∨ a = a
idr∨    ∀ a ∈ Bool :                                            a ∨ false = a
ass∨    ∀ a , b , c ∈ Bool :                                    (a ∨ b) ∨ c = a ∨ (b ∨ c)
comm∨   ∀ a , b ∈ Bool :                                        a ∨ b = b ∨ a
null∨   ∨ a ∈ Bool :                                            true ∨ a = true
dist∧   ∀ a , b , c ∈ Bool :                                    a ∧ (b ∨ c) = a ∧ b ∨ a ∧ c
dist∨   ∀ a , b , c ∈ Bool :                                    a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c)
abs∧    ∀ a , b ∈ Bool :                                        a ∧ (a ∧ b) = a
abs∨    ∀ a , b ∈ Bool :                                        a ∨ (a ∧ b) = a

Műveletek:
x ∧ y = ha x akkor y különben false
x ∨ y = ha x akkor true különben y

Egyéb függvények:
eqb(a , b) : Bool × Bool ↦ Bool     a = b
Eqb(a , b) : Bool × Bool ↦ 𝕃        a = b
