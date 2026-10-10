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

- problem_id: E298
- collection: erdos
- question_id: erdos:298
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/298.lean#erdos_298
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does every set $A \subseteq \mathbb{N}$ of positive density contain some finite $S \subset A$ such that $\sum_{n \in S} \frac{1}{n} = 1$? The answer is yes, proved by Bloom [Bl21] (even if 'positive density' is interpreted as 'positive upper density', which is likely what Erdős intended). The theorem below uses the positive-upper-density interpretation; the literal natural-density interpretation is recorded separately. This was formalized in Lean 3 by Bloom and Mehta.
- notes: Erdos Problem 298 -- https://www.erdosproblems.com/298
- track: solved
- answer_shape: decide
- source_stem: 298
- mathdb_ref: erdos:298
- source_namespace: Erdos298
- source_theorem: erdos_298
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ (∀ (A : Set ℕ), 0 ∉ A → 0 < A.upperDensity →
        ∃ (S : Finset ℕ), ↑S ⊆ A ∧ ∑ n ∈ S, (1 / n : ℚ) = 1)

end Problem
