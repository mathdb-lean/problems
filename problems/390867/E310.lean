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

- problem_id: E310
- collection: erdos
- question_id: erdos:310
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/310.lean#erdos_310
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\alpha >0$ and $N\geq 1$. Is it true that for any $A\subseteq \{1,\ldots,N\}$ with $\lvert A\rvert \geq \alpha N$ there exists some $S\subseteq A$ such that $$\frac{a}{b}=\sum_{n\in S}\frac{1}{n}$$ with $a\leq b =O_\alpha(1)$? Liu and Sawhney [LiSa24] observed that the main result of Bloom [Bl21] implies a positive solution to this conjecture. They prove a more precise version, that if $(\log N)^{-1/7+o(1)}\leq \alpha \leq 1/2$ then there is some $S\subseteq A$ such that $\frac{a}{b}=\sum_{n\in S}\frac{1}{n}$ with $a\leq b \leq \exp(O(1/\alpha))$. They also observe that the dependence $b\leq \exp(O(1/\alpha))$ is sharp.
- notes: Erdos Problem 310 -- https://www.erdosproblems.com/310
- track: solved
- answer_shape: decide
- source_stem: 310
- mathdb_ref: erdos:310
- source_namespace: Erdos310
- source_theorem: erdos_310
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ α : ℝ, 0 < α → ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N →
        ∀ A ⊆ Finset.Icc 1 N, α * N ≤ A.card →
          ∃ S ⊆ A, ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ C ∧ ∑ n ∈ S, (1 / n : ℚ) = a / b

end Problem
