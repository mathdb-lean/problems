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

- problem_id: RSizeOrderConnectedDomination_mukwembi_theorem_2_1
- collection: paper
- question_id: paper:SizeOrderConnectedDomination
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/SizeOrderConnectedDomination.lean#mukwembi_theorem_2_1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Theorem 2.1** of [S. Mukwembi, _Size, order, and connected domination_, Canad. Math. Bull. 57 (2014), no. 1, 141–144](https://doi.org/10.4153/CMB-2013-020-5) claims: if $G$ is a connected triangle-free graph of order $n$ and size $m$ with connected domination number $\gamma_c$, then $$m \le \frac{(n - \gamma_c)^2}{4} + n - 1.$$ The claim is **false**: the 3-dimensional hypercube $Q_3$ is a counterexample, with $n = 8$, $m = 12$ and $\gamma_c = 4$, so the asserted bound reads $12 \le (8-4)^2/4 + 8 - 1 = 11$. The gap in the paper's proof (p. 143) is the unjustified assertion that there is an edge $uv$ with $\gamma_c(G) \le \gamma_c(G - \{u, v\})$: in $Q_3$, removing any adjacent pair of vertices leaves a graph with connected domination number $2 < 4$. The corollaries of the paper (Corollary 2.2 and 2.3, on leaf numbers of triangle-free graphs) remain true; Corollary 2.2 is Graffiti.pc Conjecture 1.1, recorded as `WrittenOnTheWallII.GraphConjecture2.conjecture2`.
- notes: Problem from SizeOrderConnectedDomination -- https://doi.org/10.4153/CMB-2013-020-5
- track: solved
- answer_shape: decide
- source_stem: SizeOrderConnectedDomination
- source_namespace: SizeOrderConnectedDomination
- source_theorem: mukwembi_theorem_2_1
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open SimpleGraph

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
          (G : SimpleGraph α) [DecidableRel G.Adj],
          G.Connected → G.CliqueFree 3 →
          (G.edgeFinset.card : ℝ) ≤
            ((Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ)) ^ 2 / 4
              + (Fintype.card α : ℝ) - 1

end Problem
