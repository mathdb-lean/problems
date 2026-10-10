/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

-- Ported 2026-10-08 to Mathlib d13f23b7 (Lean 4.34.1). Mathlib now ships
-- `Nat.maxPrimeFac` and this file's lemmas as `Mathlib.Data.Nat.MaxPrimeFac`
-- (Bo Cowgill), so the vendored definition and every lemma Mathlib also states
-- were removed here: a module may not redeclare what its imports declare.
-- Mathlib's `prime_maxPrimeFac_of_one_lt` and `one_lt_maxPrimeFac_iff` take `n`
-- implicitly where the vendored versions took it explicitly; `maxPrimeFac 1 = 1`
-- and `maxPrimeFac 0 = 0` are unchanged. The two names Mathlib does not have are
-- kept below so that files written against the vendored module still elaborate.
public import Mathlib.Data.Nat.MaxPrimeFac

@[expose] public section

namespace Nat

example : maxPrimeFac 0 = 0 := by decide +kernel
example : maxPrimeFac 1 = 1 := by decide +kernel
example : maxPrimeFac 12 = 3 := by decide +kernel
example : maxPrimeFac 97 = 97 := by decide +kernel
example : maxPrimeFac 125 = 5 := by decide +kernel
example : maxPrimeFac 360 = 5 := by decide +kernel

lemma maxPrimeFac_eq_of_dvd_of_le
    (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h_dvd : p ∣ n) (h_le : maxPrimeFac n ≤ p) :
    maxPrimeFac n = p :=
  le_antisymm h_le (le_maxPrimeFac hn.ne' hp h_dvd)

/-- The greatest prime factor of a natural number greater than one is the least upper bound of
its prime factors. Mathlib states the same fact as `Nat.isLUB_maxPrimeFac`. -/
lemma isLeast_maxPrimeFac {n : ℕ} (hn : 1 < n) :
    IsLeast (upperBounds {p : ℕ | p.Prime ∧ p ∣ n}) (maxPrimeFac n) :=
  isLUB_maxPrimeFac hn

end Nat
