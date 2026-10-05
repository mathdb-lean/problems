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

- problem_id: O287616_conjecture
- collection: oeis
- question_id: oeis:287616
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/287616.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Zhi-Wei Sun's Conjecture (A287616)**: Any nonnegative integer can be written as the sum of a triangular number $x(x+1)/2$, a generalized pentagonal number $y(3y+1)/2$, and a generalized heptagonal number $z(5z+1)/2$, where $x, y, z$ are nonnegative integers. This was proved in [CGQFG26].
- notes: OEIS A287616 -- https://oeis.org/A287616
- track: solved
- answer_shape: proof
- source_stem: 287616
- source_namespace: OeisA287616
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The predicate that `n` can be written as $x(x+1)/2 + y(3y+1)/2 + z(5z+1)/2$ for
nonnegative integers $x, y, z$. -/
def A (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (3 * y + 1) / 2 + z * (5 * z + 1) / 2

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : A 0 :=
  ⟨0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_1 : A 1 :=
  ⟨1, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, 1, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨2, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨1, 0, 1, by norm_num⟩

abbrev Target : Prop :=
    ∀ (n : ℕ),
      A n

end Problem
