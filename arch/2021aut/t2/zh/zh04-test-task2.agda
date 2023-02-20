module zh04-test-task2 where
open import lib
open import zh04 using (task2)

test-task2-1 : Eq ℕ (task2 0 0) 0
test-task2-1 = refl -- 0 * 0 = 0

test-task2-2 : Eq ℕ (task2 0 5) 0
test-task2-2 = refl -- 0 * 5 = 0

test-task2-3 : Eq ℕ (task2 5 0) 0
test-task2-3 = refl -- 5 * 0 = 0

test-task2-4 : Eq ℕ (task2 1 5) 5
test-task2-4 = refl -- 1 * 5 = 5

test-task2-5 : Eq ℕ (task2 5 1) 5
test-task2-5 = refl -- 5 * 1 = 5

test-task2-6 : Eq ℕ (task2 2 3) 6
test-task2-6 = refl -- 2 * 3 = 6

test-task2-7 : Eq ℕ (task2 3 2) 6
test-task2-7 = refl -- 3 * 2 = 6
