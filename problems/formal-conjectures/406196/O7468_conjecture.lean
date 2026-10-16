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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: O7468_conjecture
- collection: oeis
- question_id: oeis:7468
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/7468.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The only positive integer $n$ such that $a(n)$ is a perfect square is $n=38$. - Carlos Eduardo Olivieri, Mar 09 2015
- notes: OEIS A7468 -- https://oeis.org/A7468
- track: open
- answer_shape: proof
- source_stem: 7468
- source_namespace: OeisA7468
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Sum of the next $n$ primes, with $a(0) = 0$. -/
noncomputable def a (n : ℕ) : ℕ :=
  let startIdx : ℕ := (n * (n - 1)) / 2
  ∑ i ∈ Finset.range n, Nat.nth Nat.Prime (startIdx + i)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  dsimp [a]
  rw [Finset.sum_singleton, add_zero, Nat.nth_prime_zero_eq_two]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 8 := by
  dsimp [a]
  rw [Finset.sum_range_succ, Finset.sum_range_one, add_zero, Nat.nth_prime_one_eq_three,
    show (1 + 1 : ℕ) = 2 by rfl, Nat.nth_prime_two_eq_five]

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 31 := by
  dsimp [a]
  have h5 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (by decide : Nat.Prime 13)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, add_zero,
    Nat.nth_prime_three_eq_seven, show (3 + 1 : ℕ) = 4 by rfl, Nat.nth_prime_four_eq_eleven,
    show (3 + 2 : ℕ) = 5 by rfl, h5]

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 0 < n),
      IsSquare (a n) ↔ n = 38

end Problem
