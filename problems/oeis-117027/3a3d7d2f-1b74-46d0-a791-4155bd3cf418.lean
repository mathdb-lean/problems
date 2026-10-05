/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: O117027_conjecture
- collection: oeis
- question_id: oeis:117027
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/117027.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: This suggests the ratio is approaching a limit close to 0.87. Formalized as: The sequence of ratios $P(N)/Neg(N)$ converges to a limit L, and L is in the interval (0.8, 0.9).
- notes: OEIS A117027 -- https://oeis.org/A117027
- track: open
- answer_shape: proof
- source_stem: 117027
- source_namespace: OeisA117027
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: nth_prime_five nth_prime_six nth_prime_seven nth_prime_eight nth_prime_nine nth_prime_ten nth_prime_eleven a_0 a_1 a_2 a_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat Int Filter

/-- a n is the determinant of a 2x2 matrix of non-overlapping blocks of 4 consecutive primes. -/
noncomputable def a (n : ℕ) : ℤ :=
  if 0 < n then
    let k := 4 * n
    let pPrime (i : ℕ) : ℤ := (Nat.nth Nat.Prime i : ℤ)

    let p₁ := pPrime (k - 4) -- p_{4n-4} in 0-indexed Mathlib
    let p₂ := pPrime (k - 1) -- p_{4n-1} in 0-indexed Mathlib
    let p₃ := pPrime (k - 3) -- p_{4n-3} in 0-indexed Mathlib
    let p₄ := pPrime (k - 2) -- p_{4n-2} in 0-indexed Mathlib

    p₁ * p₂ - p₃ * p₄
  else
    0

/-- The count of positive terms among $a(1)$, ..., $a(N)$. -/
noncomputable def positiveCount (N : ℕ) : ℕ :=
  (List.range N).countP (fun n => 0 < a (n + 1))

/-- The count of negative terms among $a(1)$, ..., $a(N)$. -/
noncomputable def negativeCount (N : ℕ) : ℕ :=
  (List.range N).countP (fun n => a (n + 1) < 0)

/-- The sequence of ratios $P(N)/Neg(N)$ as a sequence of real numbers. -/
noncomputable def ratioSeq (N : ℕ) : ℝ :=
  if negativeCount N = 0 then
    0
  else
    (positiveCount N : ℝ) / (negativeCount N : ℝ)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : (13).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : (17).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : (19).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h1 : (23).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h1 : (29).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_ten : Nat.nth Nat.Prime 10 = 31 := by
  have h1 : (31).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_eleven : Nat.nth Nat.Prime 11 = 37 := by
  have h1 : (37).Prime := by decide
  exact Nat.nth_count h1

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = -1 := by
  dsimp [a]
  rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
      Nat.nth_prime_three_eq_seven]
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = -12 := by
  dsimp [a]
  rw [Nat.nth_prime_four_eq_eleven, nth_prime_seven, nth_prime_five, nth_prime_six]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = -48 := by
  dsimp [a]
  rw [nth_prime_eight, nth_prime_eleven, nth_prime_nine, nth_prime_ten]
  norm_num

abbrev Target : Prop :=
    ∃ L : ℝ, Tendsto ratioSeq atTop (nhds L) ∧ 0.8 < L ∧ L < 0.9

end Problem
