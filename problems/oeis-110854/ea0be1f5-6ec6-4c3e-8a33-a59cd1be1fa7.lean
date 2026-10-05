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

- problem_id: O110854_conjecture
- collection: oeis
- question_id: oeis:110854
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/110854.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Do the absolute values cover A004275? A004275 is $1$ together with the nonnegative even numbers. The conjecture asks whether every member of A004275 occurs as $|a(n)|$ for some term of the sequence.
- notes: OEIS A110854 -- https://oeis.org/A110854
- track: open
- answer_shape: proof
- source_stem: 110854
- source_namespace: OeisA110854
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: nth_prime_five nth_prime_six nth_prime_seven nth_prime_eight nth_prime_nine a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat

/--
The primary defining sequence `a`.
$a(n)$ is $\mathrm{prime}(2n+2) - \mathrm{prime}(2n+1) - \mathrm{prime}(2n) + \mathrm{prime}(2n-1)$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let p (k : ℕ) : ℤ := (Nat.nth Nat.Prime (k - 1)).cast
  if n = 0 then 0
  else p (2 * n + 2) - p (2 * n + 1) - p (2 * n) + p (2 * n - 1)

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

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  dsimp [a]
  rw [nth_prime_five, Nat.nth_prime_four_eq_eleven, Nat.nth_prime_three_eq_seven,
    Nat.nth_prime_two_eq_five]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  dsimp [a]
  rw [nth_prime_seven, nth_prime_six, nth_prime_five, Nat.nth_prime_four_eq_eleven]
  norm_num

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by
  dsimp [a]
  rw [nth_prime_nine, nth_prime_eight, nth_prime_seven, nth_prime_six]
  norm_num

abbrev Target : Prop :=
    ∀ d : ℕ, (d = 1 ∨ Even d) → ∃ n > 0, d = (a n).natAbs

end Problem
