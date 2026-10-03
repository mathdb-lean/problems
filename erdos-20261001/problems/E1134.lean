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

- problem_id: E1134
- collection: erdos
- question_id: erdos:1134
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1134.lean#erdos_1134
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{N}$ be the smallest set which contains $1$ and is closed under the operations $$x\mapsto 2x+1,\quad x\mapsto 3x+1,\quad x\mapsto 6x+1.$$ Does $A$ have positive lower density? Lagarias [La16] reports that Erdős asked this in 1972, offering £10 for a solution. (Although Hilton told Lagarias that this problem may have been formulated by Klarner, and that Erdős liked it and offered a prize for its solution.) Erdős had earlier proved (as reported in [KlRa74]) that if $A$ is the smallest set which contains $1$ and is closed under the operations $x\mapsto m_ix+b_i$ for some (possibly infinite) collection of $m_i\geq 1$ and $b_i\geq 0$ then, if $\sigma>0$ is such that $\sum \frac{1}{m_i^\sigma}=1$ then, for all large $X$, $\lvert A\cap [1,X]\rvert \ll X^{\sigma+o(1)}$. This result does not help with the given problem since $\frac{1}{2}+\frac{1}{3}+\frac{1}{6}=1$. This was answered in the negative soon afterwards by Crampin and Hilton (as reported in [Kl82]), who proved that in fact, for all large $X$, $\lvert A\cap [1,X]\rvert \ll X^{\tau+o(1)}$ where $\tau\approx 0.900626$ is the unique positive root of $$6^{-\tau}+\sum_{k\geq 0}(3\cdot 2^k)^{-\tau}=1.$$ Their proof is given in [La16]. This problem is repeated by Guy [Gu83b] in an article called 'Don't Try to Solve These Problems'. This is Problem E36 in Guy's collection [Gu04].
- notes: Erdos Problem 1134 -- https://www.erdosproblems.com/1134
- track: solved
- answer_shape: decide
- source_stem: 1134
- mathdb_ref: erdos:1134
- source_namespace: Erdos1134
- source_theorem: erdos_1134
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

/-- The smallest set of natural numbers which contains `1` and is closed under the operations
`x ↦ 2x + 1`, `x ↦ 3x + 1` and `x ↦ 6x + 1`. -/
def A : Set ℕ :=
  ⋂₀ {S : Set ℕ | 1 ∈ S ∧ ∀ x ∈ S, 2 * x + 1 ∈ S ∧ 3 * x + 1 ∈ S ∧ 6 * x + 1 ∈ S}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ 0 < A.lowerDensity

end Problem
