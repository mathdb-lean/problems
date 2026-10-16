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

- problem_id: O5153_conjecture
- collection: oeis
- question_id: oeis:5153
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/5153.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: every odd number, beginning with 3, is the sum of a prime number and a practical number. - Hal M. Switkay, Jan 28 2023
- notes: OEIS A5153 -- https://oeis.org/A5153
- track: open
- answer_shape: proof
- source_stem: 5153
- source_namespace: OeisA5153
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_4 a_6 a_8
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- A positive integer $n$ is practical if every $m \le n$ can be represented as a sum of
distinct divisors of $n$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ Nat.IsPractical n

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- $1$ is a practical number. -/
@[category test, AMS 11]
theorem a_1 : A 1 := by
  refine ⟨by decide, fun m hm => ?_⟩
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩

/-- $2$ is a practical number. -/
@[category test, AMS 11]
theorem a_2 : A 2 := by
  refine ⟨by decide, fun m hm => ?_⟩
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩
  · exact ⟨{2}, by simp, by simp⟩

/-- $4$ is a practical number. -/
@[category test, AMS 11]
theorem a_4 : A 4 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hd : Nat.divisors 4 = {1, 2, 4} := by decide
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{2}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{1, 2}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{4}, by rw [hd, Finset.coe_subset]; decide, by simp⟩

/-- $6$ is a practical number. -/
@[category test, AMS 11]
theorem a_6 : A 6 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hd : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{2}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{3}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{1, 3}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{2, 3}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{6}, by rw [hd, Finset.coe_subset]; decide, by simp⟩

/-- $8$ is a practical number. -/
@[category test, AMS 11]
theorem a_8 : A 8 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{2}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{1, 2}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{4}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{1, 4}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{2, 4}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{1, 2, 4}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{8}, by rw [hd, Finset.coe_subset]; decide, by simp⟩

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n),
      ∃ p q : ℕ, p.Prime ∧ A q ∧ n = p + q

end Problem
