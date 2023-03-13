open import lib hiding (_⊎_; inl; inr; case; ⊥; exfalso)

-- ez az eloadas 5 perccel rovidebb

-- ⊎, CustRef, OrdNum, ugyanaz a szam; ∪ vs. ⊎

-- ×, curry, uncurry, izomorfizmus

-- ⊤, ⊥, Bool=⊤+⊤

-- finite type isos

-- Bool using data

-- Nat, Maybe, pred, zerosuc, rekurzio(double,_+_,_*_,ack), iterator, rekurzor
{-
ack 0 m n = suc n
ack 1 m n = m + n
ack 2 m n = m * n
ack 3 m n = m ^ n

ack zero                         m n       = suc n
ack (suc zero)                   m zero    = m
ack (suc (suc zero))             m zero    = 0
ack (suc (suc (suc zero)))       m zero    = 1
ack (suc (suc (suc (suc zero)))) m zero    = m
ack (suc l)                      m (suc n) = ack l m (ack (suc l) m n)

-}

-- List(length,sum,map,ite,rec), Expr(eval), RoseTree(countNodes)
