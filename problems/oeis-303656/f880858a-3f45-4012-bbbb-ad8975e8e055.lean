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

- problem_id: O303656_conjecture
- collection: oeis
- question_id: oeis:303656
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/303656.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Zhi-Wei Sun's Conjecture (A303656)**: Any integer $n > 1$ can be written as the sum of two squares, a power of 3, and a power of 5.
- notes: OEIS A303656 -- https://oeis.org/A303656
- track: open
- answer_shape: proof
- source_stem: 303656
- source_namespace: OeisA303656
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_2 a_3 a_4 a_5 a_6 a_25
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The predicate that `n` can be written as $a^2 + b^2 + 3^c + 5^d$ for nonnegative integers. -/
def A (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + 3 ^ c + 5 ^ d

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, 0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨1, 0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨1, 1, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_5 : A 5 :=
  ⟨0, 1, 1, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_6 : A 6 :=
  ⟨0, 0, 0, 1, by norm_num⟩

@[category test, AMS 11]
theorem a_25 : A 25 :=
  ⟨1, 4, 1, 1, by norm_num⟩

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 1 < n),
      A n

end Problem
