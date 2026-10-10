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

- problem_id: E490
- collection: erdos
- question_id: erdos:490
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/490.lean#erdos_490
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A,B\subseteq \{1,\ldots,N\}$ be such that all the products $ab$ with $a\in A$ and $b\in B$ are distinct. Is it true that $$\lvert A\rvert \lvert B\rvert \ll \frac{N^2}{\log N}?$$ This would be best possible, for example letting $A=[1,N/2]\cap \mathbb{N}$ and $B=\{ N/2<p\leq N: p\textrm{ prime}\}$. This is true, and was proved by Szemerédi [Sz76]. In [Er72] Erdős goes on to ask whether $$\lim_{N\to \infty}\max_{A,B\subseteq [N]}\frac{\lvert A\rvert\lvert B\rvert\log N}{N^2}$$ exists, where the maximum is over $A$ and $B$ with all the products $ab$ distinct, and to determine its value. As noted in the comments to [896](https://www.erdosproblems.com/896) by van Doorn, if the limit exists it must be $\geq 1$. See also [425](https://www.erdosproblems.com/425) and [896](https://www.erdosproblems.com/896).
- notes: Erdos Problem 490 -- https://www.erdosproblems.com/490
- track: solved
- answer_shape: decide
- source_stem: 490
- mathdb_ref: erdos:490
- source_namespace: Erdos490
- source_theorem: erdos_490
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
        ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
          (∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B, a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂) →
            (A.card * B.card : ℝ) ≤ C * N ^ 2 / Real.log N

end Problem
