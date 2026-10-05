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

- problem_id: X2507_17780_4_tx_graffiti_conjecture_4
- collection: arxiv
- question_id: arxiv:2507.17780/4
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/2507.17780/4.lean#tx_graffiti_conjecture_4
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: TxGraffiti [Conjecture 4](https://arxiv.org/abs/2507.17780): for every nontrivial connected graph $G$, the saturation number is at most the harmonic index, $\mu^*(G) \le H(G)$. This conjecture is **FALSE**. **Counterexample.** The friendship graph $F_4$ (`friendshipF4`) is connected and nontrivial, with $\mu^*(F_4) = 4$ and $H(F_4) = 18/5$. Indeed the four rim edges $\{1,2\}, \{3,4\}, \{5,6\}, \{7,8\}$ form a maximal matching of size $4$, and no maximal matching is smaller, so $\mu^*(F_4) = 4$; the eight spokes contribute $2/(8+2) = 1/5$ each and the four rim edges contribute $2/(2+2) = 1/2$ each, giving $H(F_4) = 8 \cdot 1/5 + 4 \cdot 1/2 = 18/5$. Since $4 > 18/5$, the bound fails. More generally the friendship graphs $F_k$ satisfy $\mu^*(F_k) = k$ and $H(F_k) = 2k/(k+1) + k/2$, so the conjecture fails for every $k \ge 4$. An exhaustive search confirms that $F_4$ is the smallest counterexample (order $9$). The unbounded separation was first shown by Bıyıkoğlu, whose family of edges joined to an independent set makes $\mu^*/H$ arbitrarily large; the windmill generalisation and its exact limit appear in [arXiv:2606.15761](https://arxiv.org/abs/2606.15761).
- notes: arXiv 2507.17780/4 -- https://arxiv.org/abs/2507.17780
- track: solved
- answer_shape: decide
- source_stem: 2507.17780/4
- source_namespace: Arxiv.«2507.17780»
- source_theorem: tx_graffiti_conjecture_4
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: false
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open SimpleGraph

namespace Problem

/-- The friendship graph $F_4$: a hub vertex $0$ joined to four triangles, whose
rims are the pairs $\{1,2\}, \{3,4\}, \{5,6\}, \{7,8\}$. It has $12$ edges on
$9$ vertices ($8$ spokes and $4$ rim edges). -/
def friendshipF4 : SimpleGraph (Fin 9) := fromEdgeSet {
  s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(0, 6), s(0, 7), s(0, 8),
  s(1, 2), s(3, 4), s(5, 6), s(7, 8) }

instance : DecidableRel friendshipF4.Adj := by unfold friendshipF4; infer_instance

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
          [DecidableRel G.Adj] (_hConn : G.Connected),
          (G.saturationNumber : ℚ) ≤ G.harmonicIndex

end Problem
