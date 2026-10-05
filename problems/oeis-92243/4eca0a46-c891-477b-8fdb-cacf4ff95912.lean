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

- problem_id: O92243_conjecture5_prove
- collection: oeis
- question_id: oeis:92243
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/92243.lean#conjecture5
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is the score $a(n) < 0$ for infinitely many values of $n$?
- notes: OEIS A92243 -- https://oeis.org/A92243
- track: open
- answer_shape: prove
- pair_id: O92243_conjecture5
- pair_role: prove
- source_stem: 92243
- source_namespace: OeisA92243
- source_theorem: conjecture5
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The $n$-th prime gap $g(n) = p_n - p_{n-1}$ for $n \ge 1$,
where $p_i$ is the $i$-th prime (0-indexed). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

/-- Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n ≤ 1 then 0
  else
    ∑ k ∈ Finset.Icc 2 n,
      ((primeGap k : ℤ) - (primeGap (k - 1) : ℤ)).sign

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  unfold a
  have h2 : ¬ 2 ≤ 1 := by decide
  rw [if_neg h2]
  have h_icc : Finset.Icc 2 2 = {2} := by decide
  rw [h_icc, Finset.sum_singleton]
  unfold primeGap
  have h_zero : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h_one : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have h_two : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  rw [h_zero, h_one, h_two]
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  unfold a
  have h3 : ¬ 3 ≤ 1 := by decide
  rw [if_neg h3]
  have h_icc : Finset.Icc 2 3 = {2, 3} := by decide
  rw [h_icc, Finset.sum_pair (by decide)]
  unfold primeGap
  have h_zero : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h_one : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have h_two : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  have h_three : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  rw [h_zero, h_one, h_two, h_three]
  decide

abbrev Target : Prop :=
    Set.Infinite {n : ℕ | a n < 0}

end Problem
