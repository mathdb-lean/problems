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

- problem_id: O306477_conjecture
- collection: oeis
- question_id: oeis:306477
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/306477.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Zhi-Wei Sun's 2-4-6-8 Conjecture (A306477)**: Any integer $n > 0$ can be written as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$ for nonnegative integers $w, x, y, z$. This is false: $n = 896315812331399$ is a counterexample. See T. Adamczewski, OEIS Open: How many conjectures can language models turn into theorems?, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941).
- notes: OEIS A306477 -- https://oeis.org/A306477
- track: solved
- answer_shape: proof
- source_stem: 306477
- source_namespace: OeisA306477
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5 a_6
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The predicate that `n` can be written as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
for nonnegative integers $w, x, y, z$. -/
def A (n : ℕ) : Prop :=
  ∃ w x y z : ℕ, n = (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_1 : A 1 :=
  ⟨0, 0, 0, 0, by decide⟩

@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, 1, 0, 0, by decide⟩

@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨1, 0, 0, 0, by decide⟩

@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨1, 1, 0, 0, by decide⟩

@[category test, AMS 11]
theorem a_5 : A 5 :=
  ⟨1, 1, 1, 0, by decide⟩

@[category test, AMS 11]
theorem a_6 : A 6 :=
  ⟨2, 0, 0, 0, by decide⟩

abbrev Target : Prop :=
    ¬ ∀ n : ℕ, 0 < n → A n

end Problem
