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

- problem_id: O110475_conjecture
- collection: oeis
- question_id: oeis:110475
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/110475.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: It is conjectured that $1,2,3,4,5,6,7,9,11$ are the only positive integers which cannot be represented as the sum of two elements of indices $n$ such that $a(n) = 1$.
- notes: OEIS A110475 -- https://oeis.org/A110475
- track: open
- answer_shape: proof
- source_stem: 110475
- source_namespace: OeisA110475
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The primary defining sequence `a`.
$a(n)$ is the number of symbols '*' and '^' to write the canonical prime factorization of $n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let f := Nat.factorization n
  let s := f.support
  let numDistinctPrimes := s.card
  let numAsterisks := numDistinctPrimes - 1
  let numCarets := (s.filter fun p => f p > 1).card
  numAsterisks + numCarets

/-- The set of exceptional integers. -/
def exceptionalSet : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 9, 11}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  dsimp [a]
  simp

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  dsimp [a]
  have h2 : Nat.Prime 2 := by decide
  rw [Nat.Prime.factorization h2]
  simp

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  dsimp [a]
  have h3 : Nat.Prime 3 := by decide
  rw [Nat.Prime.factorization h3]
  simp

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  dsimp [a]
  have : (4 : ℕ) = 2 ^ 2 := by rfl
  rw [this, Nat.Prime.factorization_pow (by decide)]
  simp [Finset.filter_singleton]

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by
  dsimp [a]
  have h5 : Nat.Prime 5 := by decide
  rw [Nat.Prime.factorization h5]
  simp

abbrev Target : Prop :=
    ∀ m > 0, m ∉ exceptionalSet ↔ ∃ x y : ℕ, a x = 1 ∧ a y = 1 ∧ m = x + y

end Problem
