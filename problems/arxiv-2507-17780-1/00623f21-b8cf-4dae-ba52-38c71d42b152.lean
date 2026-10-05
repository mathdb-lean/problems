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

- problem_id: X2507_17780_1_tx_graffiti_conjecture_1
- collection: arxiv
- question_id: arxiv:2507.17780/1
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/2507.17780/1.lean#tx_graffiti_conjecture_1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: TxGraffiti [Conjecture 1](https://arxiv.org/abs/2507.17780): for every nontrivial connected graph $G$ with $\Delta(G) \ge 2$, $$\alpha(G) \ge \frac{a(G) + R(G)}{\Delta(G)}.$$ This conjecture is **true**. **Proof sketch.** Substitute the Caro–Wei lower bound $\alpha \ge W$ for $\alpha$ and reduce to $a \le (\Delta - 1) \alpha$. The case $\Delta = 2$ is trivial ($a = \alpha$). For $\Delta \ge 4$ an AM–HM argument with $m \le (n - a)\Delta$ yields a quadratic whose discriminant is negative. For $\Delta = 3$ the annihilation number has a closed form in the degree counts $(n_1, n_2, n_3)$ and $a \le 2W$ is verified in three regimes. See [arXiv:2606.29553](https://arxiv.org/abs/2606.29553).
- notes: arXiv 2507.17780/1 -- https://arxiv.org/abs/2507.17780
- track: solved
- answer_shape: proof
- source_stem: 2507.17780/1
- source_namespace: Arxiv.«2507.17780»
- source_theorem: tx_graffiti_conjecture_1
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph

namespace Problem

abbrev Target : Prop :=
    ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected)
        (_hDeg : 2 ≤ G.maxDegree),
      (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum

end Problem
