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

- problem_id: E147
- collection: erdos
- question_id: erdos:147
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/147.lean#erdos_147
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $H$ is bipartite with minimum degree $r$ then there exists $\epsilon=\epsilon(H)>0$ such that $$\mathrm{ex}(n;H) \gg n^{2-\frac{1}{r-1}+\epsilon}.$$ Conjectured by Erdős and Simonovits [ErSi84]. A probabilistic argument shows that there exists some $\epsilon=\epsilon(H)>0$ such that $\mathrm{ex}(n;H) \gg n^{2-\frac{2}{r}+\epsilon}$. This conjecture was disproved by Janzer [Ja23] for even $r\geq 4$. The case $r=3$ was disproved by Janzer [Ja23b], who constructed, for any $\epsilon>0$, a $3$-regular bipartite graph $H$ such that $\mathrm{ex}(n;H)\ll n^{\frac{4}{3}+\epsilon}$. In [Ja23] Janzer conjectures that the above lower bound is sharp, in that for any $r\geq 3$ and $\epsilon>0$ there exists an $r$-regular graph $H$ such that $\mathrm{ex}(n;H) \ll n^{2-\frac{2}{r}+\epsilon}$. Janzer's result proves this for even $r\geq 4$. See also [113](https://www.erdosproblems.com/113), [146](https://www.erdosproblems.com/146), and [714](https://www.erdosproblems.com/714). The conjecture is stated for minimum degree $r \geq 2$ (for $r = 1$ the exponent $2 - \frac{1}{r-1}$ is not meaningful).
- notes: Erdos Problem 147 -- https://www.erdosproblems.com/147
- track: solved
- answer_shape: decide
- source_stem: 147
- mathdb_ref: erdos:147
- source_namespace: Erdos147
- source_theorem: erdos_147
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Asymptotics SimpleGraph

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (V : Type) [Fintype V] [Nonempty V] (H : SimpleGraph V) [DecidableRel H.Adj],
          H.IsBipartite → 2 ≤ H.minDegree → ∃ ε : ℝ, 0 < ε ∧
            (fun n : ℕ => (n : ℝ) ^ (2 - 1 / ((H.minDegree : ℝ) - 1) + ε)) =O[atTop]
              fun n : ℕ => (extremalNumber n H : ℝ)

end Problem
