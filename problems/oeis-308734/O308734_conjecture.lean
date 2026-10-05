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

- problem_id: O308734_conjecture
- collection: oeis
- question_id: oeis:308734
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/308734.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Zhi-Wei Sun's Four-Square Conjecture (A308734)**: Any integer $n > 1$ can be written as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$ for nonnegative integers $a, b, c, d, x, y$.
- notes: OEIS A308734 -- https://oeis.org/A308734
- track: open
- answer_shape: proof
- source_stem: 308734
- source_namespace: OeisA308734
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_2 a_3 a_4 a_5 a_6
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The predicate that `n` can be written as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$
for nonnegative integers $a, b, c, d, x, y$. -/
def A (n : ℕ) : Prop :=
  ∃ a b c d x y : ℕ, n = (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, 0, 0, 0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨0, 0, 0, 0, 0, 1, by norm_num⟩

@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨0, 0, 0, 0, 1, 1, by norm_num⟩

@[category test, AMS 11]
theorem a_5 : A 5 :=
  ⟨1, 0, 0, 0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem a_6 : A 6 :=
  ⟨0, 0, 0, 0, 2, 0, by norm_num⟩

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 1 < n),
      A n

end Problem
