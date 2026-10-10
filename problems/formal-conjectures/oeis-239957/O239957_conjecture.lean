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

- problem_id: O239957_conjecture
- collection: oeis
- question_id: oeis:239957
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/239957.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Zhi-Wei Sun's Conjecture (A239957)**: Every prime $p$ has a primitive root $0 < g < p$ of the form $k^2 + 1$, where $k$ is an integer.
- notes: OEIS A239957 -- https://oeis.org/A239957
- track: open
- answer_shape: proof
- source_stem: 239957
- source_namespace: OeisA239957
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_2
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The predicate that $p$ has a primitive root $0 < g < p$ of the form $k^2 + 1$, where $k$ is an integer. -/
def A (p : ℕ) : Prop :=
  ∃ k : ℤ, k ^ 2 + 1 < p ∧ orderOf (k ^ 2 + 1 : ZMod p) = p - 1

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, by norm_num, by norm_num⟩

abbrev Target : Prop :=
    ∀ (p : ℕ) (hp : p.Prime),
      A p

end Problem
