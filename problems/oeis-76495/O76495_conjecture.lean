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

- problem_id: O76495_conjecture
- collection: oeis
- question_id: oeis:76495
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/76495.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: At present, the 0 entry for $n = 5$ is only a conjecture. That is, it is conjectured that there is no positive integer $x$ such that $\sigma_1(x) \bmod x = 5$.
- notes: OEIS A76495 -- https://oeis.org/A76495
- track: open
- answer_shape: proof
- source_stem: 76495
- source_namespace: OeisA76495
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_6
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open ArithmeticFunction

open Classical in
/-- Smallest positive integer $x$ such that $\sigma_1(x) \bmod x = n$, or $0$ if no such $x$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ x, 0 < x ∧ (sigma 1 x : ℕ) % x = n then
    Nat.find h
  else
    0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide
  · exact (h ⟨2, by decide⟩).elim

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 20 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide
  · exact (h ⟨20, by decide⟩).elim

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide
  · exact (h ⟨4, by decide⟩).elim

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 9 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide
  · exact (h ⟨9, by decide⟩).elim

/-- Value of the sequence `a` at 6. -/
@[category test, AMS 11]
theorem a_6 : a 6 = 25 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide
  · exact (h ⟨25, by decide⟩).elim

abbrev Target : Prop :=
    a 5 = 0

end Problem
