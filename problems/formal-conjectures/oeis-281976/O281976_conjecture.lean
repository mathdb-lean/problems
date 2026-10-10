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

- problem_id: O281976_conjecture
- collection: oeis
- question_id: oeis:281976
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/281976.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Zhi-Wei Sun's Conjecture (A281976)**: Any integer $n \geq 0$ can be written as $x^2 + y^2 + z^2 + w^2$ with $x, y, z, w$ nonnegative integers and $z \leq w$, such that both $x$ and $x + 24y$ are squares.
- notes: OEIS A281976 -- https://oeis.org/A281976
- track: open
- answer_shape: proof
- source_stem: 281976
- source_namespace: OeisA281976
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_8 a_12 a_23 a_24
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The predicate that `n` can be written as $x^2 + y^2 + z^2 + w^2$ with $x, y, z, w$ nonnegative
integers, $z \leq w$, such that both $x$ and $x + 24y$ are squares. -/
def A (n : ℕ) : Prop :=
  ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧ z ≤ w ∧ IsSquare x ∧ IsSquare (x + 24 * y)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : A 0 :=
  ⟨0, 0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_1 : A 1 :=
  ⟨1, 0, 0, 0, by norm_num, by norm_num, ⟨1, by norm_num⟩, ⟨1, by norm_num⟩⟩

@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨1, 0, 0, 1, by norm_num, by norm_num, ⟨1, by norm_num⟩, ⟨1, by norm_num⟩⟩

@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨1, 0, 1, 1, by norm_num, by norm_num, ⟨1, by norm_num⟩, ⟨1, by norm_num⟩⟩

@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨0, 0, 0, 2, by norm_num, by norm_num, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩

@[category test, AMS 11]
theorem a_8 : A 8 :=
  ⟨0, 0, 2, 2, by norm_num, by norm_num, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩

@[category test, AMS 11]
theorem a_12 : A 12 :=
  ⟨1, 1, 1, 3, by norm_num, by norm_num, ⟨1, by norm_num⟩, ⟨5, by norm_num⟩⟩

@[category test, AMS 11]
theorem a_23 : A 23 :=
  ⟨1, 2, 3, 3, by norm_num, by norm_num, ⟨1, by norm_num⟩, ⟨7, by norm_num⟩⟩

@[category test, AMS 11]
theorem a_24 : A 24 :=
  ⟨4, 0, 2, 2, by norm_num, by norm_num, ⟨2, by norm_num⟩, ⟨2, by norm_num⟩⟩

abbrev Target : Prop :=
    ∀ (n : ℕ),
      A n

end Problem
