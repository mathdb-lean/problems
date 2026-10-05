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

- problem_id: O130911_conjecture
- collection: oeis
- question_id: oeis:130911
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/130911.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Shevelev conjectures that $a(n) \ge 0$ for $n > 3$.
- notes: OEIS A130911 -- https://oeis.org/A130911
- track: open
- answer_shape: proof
- source_stem: 130911
- source_namespace: OeisA130911
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Parity sign of binary weight: $+1$ if popcount is odd, $-1$ if even. -/
def signWeight (k : ℕ) : ℤ :=
  if (Nat.digits 2 k).sum % 2 = 1 then 1 else -1

/-- $a(n) = \sum_{i=0}^{n-1} \mathrm{signWeight}(p_i)$ where $p_i$ is the $i$-th prime. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, signWeight (Nat.nth Nat.Prime i)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  unfold a
  have h : Finset.range 1 = {0} := by decide
  rw [h, Finset.sum_singleton]
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  rw [h0]
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  unfold a
  have h : Finset.range 2 = {0, 1} := by decide
  rw [h, Finset.sum_pair (by decide)]
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  rw [h0, h1]
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by
  unfold a
  have h : Finset.range 3 = {0, 1, 2} := by decide
  rw [h]
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have h2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  rw [h0, h1, h2]
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  unfold a
  have h : Finset.range 4 = {0, 1, 2, 3} := by decide
  rw [h]
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have h2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  have h3 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide)]
  rw [h0, h1, h2, h3]
  decide

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 3 < n),
      a n ≥ 0

end Problem
