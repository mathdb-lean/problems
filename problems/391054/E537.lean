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

- problem_id: E537
- collection: erdos
- question_id: erdos:537
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/537.lean#erdos_537
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\epsilon>0$ and $N$ be sufficiently large. If $A\subseteq \{1,\ldots,N\}$ has $\lvert A\rvert \geq \epsilon N$ then must there exist $a_1,a_2,a_3\in A$ and distinct primes $p_1,p_2,p_3$ such that $$a_1p_1=a_2p_2=a_3p_3?$$ A positive answer would imply [536]. Erdős describes a construction of Ruzsa which disproves this: consider the set of all squarefree numbers of the shape $p_1\cdots p_r$ where $p_{i+1}>2p_i$ for $1\leq i<r$. This set has positive density, and hence if $A$ is its intersection with $(N/2,N)$ then $\lvert A\rvert \gg N$ for all large $N$. Suppose now that $p_1a_1=p_2a_2=p_3a_3$ where $a_i\in A$ and $p_1,p_2,p_3$ are distinct primes. Without loss of generality we may assume that $a_2>a_3$ and hence $p_2<p_3$, and so since $p_2p_3\mid a_1\in A$ we must have $2<p_3/p_2$. On the other hand $p_3/p_2=a_2/a_3\in (1,2)$, a contradiction.
- notes: Erdos Problem 537 -- https://www.erdosproblems.com/537
- track: solved
- answer_shape: decide
- source_stem: 537
- mathdb_ref: erdos:537
- source_namespace: Erdos537
- source_theorem: erdos_537
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
          ∀ A ⊆ Finset.Icc 1 N, (A.card : ℝ) ≥ ε * N →
            ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ p₁ p₂ p₃ : ℕ,
              p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
              p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
              a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃

end Problem
