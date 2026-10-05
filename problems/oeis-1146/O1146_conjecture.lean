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

- problem_id: O1146_conjecture
- collection: oeis
- question_id: oeis:1146
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/1146.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: I conjecture that { $a(n)$ ; $n>1$ } are the numbers such that $n^4-1$ divides $2^n-1$, intersection of A247219 and A247165. - M. F. Hasler, Jul 25 2015 This formalizes the reverse direction.
- notes: OEIS A1146 -- https://oeis.org/A1146
- track: open
- answer_shape: proof
- source_stem: 1146
- source_namespace: OeisA1146
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 n_add_two_le_two_pow
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The primary defining sequence `a`.
$a(n) = 2^{2^n}$.
-/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 16 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 256 := by rfl

@[category API, AMS 11]
lemma n_add_two_le_two_pow (n : ℕ) (hn : 2 ≤ n) : n + 2 ≤ 2 ^ n := by
  induction' n, hn using Nat.le_induction with k hk ih
  · decide
  · calc
      k + 1 + 2 = k + 2 + 1 := by omega
      _ ≤ 2 ^ k + 1 := by exact Nat.add_le_add_right ih 1
      _ ≤ 2 ^ k + 2 ^ k := by
        apply Nat.add_le_add_left
        apply Nat.one_le_pow'
      _ = 2 ^ (k + 1) := by ring

abbrev Target : Prop :=
    ∀ k : ℕ, ((k^4 - 1) : ℕ) ∣ (2^k - 1 : ℕ) → k > 1 → ∃ n : ℕ, 2 ≤ n ∧ k = a n

end Problem
