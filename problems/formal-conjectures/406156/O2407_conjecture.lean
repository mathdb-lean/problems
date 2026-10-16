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

- problem_id: O2407_conjecture
- collection: oeis
- question_id: oeis:2407
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/2407.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: This sequence is believed to be infinite.
- notes: OEIS A2407 -- https://oeis.org/A2407
- track: open
- answer_shape: proof
- source_stem: 2407
- source_namespace: OeisA2407
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_7 a_19 a_37 a_61 a_127 not_a_91
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- A natural number is in A002407 when it is prime and is the difference of two consecutive
positive cubes. The addition equality avoids truncated subtraction in `ℕ`. -/
def A (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k > 0, p + k ^ 3 = (k + 1) ^ 3

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_7 : A 7 := by
  refine ⟨by norm_num, 1, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem a_19 : A 19 := by
  refine ⟨by norm_num, 2, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem a_37 : A 37 := by
  refine ⟨by norm_num, 3, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem a_61 : A 61 := by
  refine ⟨by norm_num, 4, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem a_127 : A 127 := by
  refine ⟨by norm_num, 6, by norm_num, by norm_num⟩

@[category test, AMS 11]
theorem not_a_91 : ¬ A 91 := by
  norm_num [A, Nat.prime_def_lt]

abbrev Target : Prop :=
    {p : ℕ | A p}.Infinite

end Problem
