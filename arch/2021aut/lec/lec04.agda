{-
(λ z → rec zero (λ x → suc (suc x)) z) 15
                                           =(függvény számítás)    (λ x → t) u = t[x↦u]
rec zero  (λ x → suc (suc x)) 15
rec zero  (λ x → suc (suc x)) (suc (suc ....(suc zero)))
                               ^ 15-szor alkalmaztam

                                           =(ℕ szamitasi suc-ra)
suc (suc (rec zero  (λ x → suc (suc x)) (suc ....(suc zero))))
                               ^ 14-szor alkalmaztam

... meg 14x

suc (suc (suc (suc ... (suc (suc (rec zero ... zero)..) = (ℕ szamitasi zero-ra)

suc (suc (suc (suc ... (suc (suc zero..) = 30 =

rec zero (λ x → suc x) 30
                                    = (fgv szamitasi)
(λ z → rec zero (λ x → suc x) z) 30	

----------

rec zero suc (suc (suc (...(suc zero)...))) = (suc (suc (...(suc zero)...)))


zero + n = n
n + zero = n



ι₁ (λ x → ι₂ (3 , x)) : (𝟚 → (ℕ ⊎ (ℕ × 𝟚))) ⊎ ⊤


ι₂ 3 : A ⊎ ℕ
ι₁ (ι₂ 3) : (A ⊎ ℕ) ⊎ B
ι₁ (ι₁ (ι₂ 3)) : ((A ⊎ ℕ)⊎B) ⊎ C

osszefoglalo
      bev       elim           szamitas                 egyediseg
𝟚     tt,ff     if-then-else   2 db                     0 db
ℕ     zero,suc  rec            2 db                     0 db
→     λ         (app)          (λx→t)u=t[x↦u]           f = λ x → f x            ((A→B)→C)→D
×     _,_       π₁,π₂          π₁(a,b)=a π₂(a,b)=b      w = π₁ w , π₂ w          rekord, pár
⊎     ι₁,ι₂     case           case(ι₁ t) u v = u t                              unió   A⊎A ≠ A , A⊎A ≅ A×𝟚
                                     ₂          v
⊤     triv                                              w = triv                 (), void
⊥               exfalso


A ⊎ ⊤    <->  A
𝟚   ket eleme van
𝟚 ⊎ ⊤   3 eleme van
(𝟚 ⊎ ⊤) ⊎ ⊤   4 eleme van   ι₁ (ι₁ ff)  ι₁ (ι₂ triv)  ι₂ triv
....
osszes veges tipus:
0-elemu   ⊥                  0
1-elemu   ⊤                  1
2-elemu   ⊤ ⊎ ⊤              2
3-elemu   ⊤ ⊎ ⊤ ⊎ ⊤          3
4-elemu   ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤      ...
....

∞-elemu   ℕ
          ℕ ⊎ ⊤


0+1=1
⊥⊎⊤ ↔ ⊤   logikai ekvivalencia, a ket tipus ekvivalens

a tipusok ugyanugy mukodnek, mint a szamok:

+   ⊎      (a+b)+c = a+(b+c)   (A ⊎ B) ⊎ C  ↔  A ⊎ (B ⊎ C)
           (a+b)   = b+a       A ⊎ B        ↔  B ⊎ A
0   ⊥      0+a = a             ⊥ ⊎ A        ↔  A
*   ×                          (A × B) × C  ↔  A × (B × C)
                               (A × B)      ↔  B × A
1   ⊤                          ⊤ × A        ↔  A
disztr     a*(b+c)=a*b+a*c     A×(B⊎C)      ↔ A×B ⊎ A×C
a^b  B→A   1^a = 1             A→⊤          ↔ ⊤
           a^1 = a             ⊤→A          ↔ A
           a^(b+c) = a^b * a^c (B⊎C)→A      ↔ (B→A)×(C→A)
           a^0 = 1             ⊥→A          ↔ ⊤
           a^(c*b) = (a^b)^c   (C×B)→A      ↔ C → B → A

2→3  3*3 = 3^2

                               A×(⊤⊎⊤)        A×⊤ ⊎ A×⊤
                               A×

(a+b)*(a+b) =diszt
(a+b)*a + (a+b)*b =komm
a*(a+b) + b*(a+b) =diszt
a*a+a*b + b*a+b*b =komm
a*a+a*b + a*b+b*b =assz
a*a+(a*b+a*b)+b*b =egys
a*a+(1*a*b+1*a*b)+b*b =diszt
a*a+(1+1)*a*b+b*b =
a*a+2*a*b+b*b
-}
open import lib

-- type a <-> b = (a -> b , b->a)
-- plusassoc ::
--    Either (Either a b) c <-> Either a (Either b c)

⊎-assoc : {A B C : Set} → (A ⊎ B) ⊎ C  ↔  A ⊎ (B ⊎ C)
⊎-assoc =
  (λ x → case x (λ ab → case ab ι₁ (λ b → ι₂ (ι₁ b)))
                (λ c → ι₂ (ι₂ c))) ,
  {!!}

+-assoc' : (⊤ ⊎ ⊥) ⊎ 𝟚  ↔  ⊤ ⊎ (⊥ ⊎ 𝟚)
+-assoc' = ⊎-assoc


⊎-comm : {A B : Set} → A ⊎ B ↔ B ⊎ A
⊎-comm = (λ ab → case ab ι₂ ι₁) , (λ ab → case ab ι₂ ι₁)

⊎idl : {A : Set} → ⊥ ⊎ A ↔ A
⊎idl = (λ w → case w (λ b → exfalso b) (λ a → a)) , ι₂

×idl : {A : Set} → ⊤ × A        ↔  A
×idl = (λ w → π₂ w) , (λ a → triv , a)

