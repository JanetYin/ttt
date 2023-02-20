
{-
A For  ----  A formula
A True ----  A formula igaz / van bizonyítása

-                       -
-----                   -------
⊤ For                   ⊤ True

-                       ⊥ True   A For
-----                   -------------        ex falso sequitur quodlibet 
⊥ For                      A True

A For   B For           A True   B True        A ∧ B True    A ∧ B True
-------------           ---------------        ----------    ----------
   A ∧ B For               A ∧ B True            A True        B True

A For   B For             A True        B True                
-------------           ----------    ----------              
  A ∨ B For             A ∨ B True    A ∨ B True

A For   B For           B True   A For         A → B True   A True
-------------           --------------         -------------------
  A → B For               A → B True                  B True


A ∨ B    A → C   B → C
----------------------     case 
      A ∨ B → C

x : B, akkor feltéve y : A, akkor λ y → x : A → B

Curry-Howard-korrespondancia

Formula        - típus
F bizonyítása  - t : F



-}

