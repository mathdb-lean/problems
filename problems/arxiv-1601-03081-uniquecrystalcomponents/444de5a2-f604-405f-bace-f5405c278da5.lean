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

- problem_id: X1601_03081_UniqueCrystalComponents_crystals_components_unique
- collection: arxiv
- question_id: arxiv:1601.03081/UniqueCrystalComponents
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/1601.03081/UniqueCrystalComponents.lean#crystals_components_unique
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $n = ab$ is a crystal, then there are no other pairs of positive integers $c, d > 1$, different from the couple $a, b$, such that $n = cd$ and $B(c, d) ∈ ℕ$, i.e., the components of the crystals are unique.
- notes: arXiv 1601.03081/UniqueCrystalComponents -- https://arxiv.org/abs/1601.03081
- track: open
- answer_shape: proof
- source_stem: 1601.03081/UniqueCrystalComponents
- source_namespace: Arxiv.«1601.03081»
- source_theorem: crystals_components_unique
- source_category: research open
- source_ams: 11 26
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: isCrystalWithComponents_35_5_7
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
An odd number $n$ is called a crystal if $n = ab$, with $a, b > 1$
and $B(a, b) ∈ ℕ$, where $B(a, b) := ((a + b)^2 + (a b + 1)^2) / (2 (a + 1) (b + 1))$.
-/
def IsCrystalWithComponents (n a b : ℕ) : Prop :=
  Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ 2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem isCrystalWithComponents_35_5_7 : IsCrystalWithComponents 35 5 7 := by
  norm_num [IsCrystalWithComponents]

abbrev Target : Prop :=
    ∀ (n a b c d : ℕ)
        (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d),
      ({a, b} : Finset ℕ) = {c, d}

end Problem
