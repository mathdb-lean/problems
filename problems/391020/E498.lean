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

- problem_id: E498
- collection: erdos
- question_id: erdos:498
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/498.lean#erdos_498
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $z_1,\ldots,z_n\in\mathbb{C}$ with $1\leq \lvert z_i\rvert$ for $1\leq i\leq n$. Let $D$ be an arbitrary disc of radius $1$. Is it true that the number of sums of the shape $$\sum_{i=1}^n\epsilon_iz_i \textrm{ for }\epsilon_i\in \{-1,1\}$$ which lie in $D$ is at most $\binom{n}{\lfloor n/2\rfloor}$? A strong form of the Littlewood-Offord problem. Erdős [Er45] proved this is true if $z_i\in\mathbb{R}$, and for general $z_i\in\mathbb{C}$ proved a weaker upper bound of $$\ll \frac{2^n}{\sqrt{n}}.$$ This was solved in the affirmative by Kleitman [Kl65], who also later generalised this to arbitrary Hilbert spaces [Kl70]. See also [395].
- notes: Erdos Problem 498 -- https://www.erdosproblems.com/498
- track: solved
- answer_shape: decide
- source_stem: 498
- mathdb_ref: erdos:498
- source_namespace: Erdos498
- source_theorem: erdos_498
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i, 1 ≤ ‖z i‖) → ∀ c : ℂ,
          {ε : Fin n → ℤ | (∀ i, ε i = -1 ∨ ε i = 1) ∧
            (∑ i, (ε i : ℂ) * z i) ∈ Metric.ball c 1}.ncard ≤ n.choose (n / 2)

end Problem
