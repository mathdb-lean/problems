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

- problem_id: E215
- collection: erdos
- question_id: erdos:215
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/215.lean#erdos_215
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist $S\subseteq \mathbb{R}^2$ such that every set congruent to $S$ (that is, $S$ after some translation and rotation) contains exactly one point from $\mathbb{Z}^2$? An old question of Steinhaus. Erdős was 'almost certain that such a set does not exist'. In fact, such a set does exist, as proved by Jackson and Mauldin [JaMa02]. Their construction depends on the axiom of choice. The plane is identified with $\mathbb{C}$: the sets congruent to $S$ are the sets $uS + t$ with $\lvert u\rvert = 1$ and $t \in \mathbb{C}$, and $\mathbb{Z}^2$ is the set of Gaussian integers.
- notes: Erdos Problem 215 -- https://www.erdosproblems.com/215
- track: solved
- answer_shape: decide
- source_stem: 215
- mathdb_ref: erdos:215
- source_namespace: Erdos215
- source_theorem: erdos_215
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ S : Set ℂ, ∀ u t : ℂ, ‖u‖ = 1 →
        ∃! z : ℂ, z ∈ (fun w => u * w + t) '' S ∧ ∃ a b : ℤ, z = a + b * Complex.I

end Problem
