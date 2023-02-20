module zh04-test-task1 where
open import lib
open import zh04 using (task1)

test-task1-1 : Eq ℕ (task1 0 0) 0
test-task1-1 = refl -- 0 + 0 = 0

test-task1-2 : Eq ℕ (task1 0 5) 5
test-task1-2 = refl -- 0 + 5 = 5

test-task1-3 : Eq ℕ (task1 5 0) 5
test-task1-3 = refl -- 5 + 0 = 5

test-task1-4 : Eq ℕ (task1 2 3) 5
test-task1-4 = refl -- 2 + 3 = 5

test-task1-5 : Eq ℕ (task1 3 2) 5
test-task1-5 = refl -- 3 + 2 = 5
