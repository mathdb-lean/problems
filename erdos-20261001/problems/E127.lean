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

- problem_id: E127
- collection: erdos
- question_id: erdos:127
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/127.lean#erdos_127
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(m)$ be maximal such that every graph with $m$ edges must contain a bipartite graph with $$\geq \frac{m}{2}+\frac{\sqrt{8m+1}-1}{8}+f(m)$$ edges. Is there an infinite sequence of $m_i$ such that $f(m_i)\to \infty$? Conjectured by Erdős, Kohayakava, and Gyárfás [Er97b]. Edwards [Ed73] proved that $f(m)\geq 0$ always. Note that $f(\binom{n}{2})= 0$, taking $K_n$. Solved by Alon [Al96], who showed $f(n^2/2)\gg n^{1/2}$, and also showed that $f(m)\ll m^{1/4}$ for all $m$. The best possible constant in $f(m)\leq Cm^{1/4}$ is unknown.
- notes: Erdos Problem 127 -- https://www.erdosproblems.com/127
- track: solved
- answer_shape: decide
- source_stem: 127
- mathdb_ref: erdos:127
- source_namespace: Erdos127
- source_theorem: erdos_127
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Asymptotics SimpleGraph

namespace Problem

/-- `f m` is the largest `k` such that every graph with `m` edges contains a bipartite subgraph
with at least $\frac{m}{2}+\frac{\sqrt{8m+1}-1}{8}+k$ edges. -/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      (m : ℝ) / 2 + (√(8 * m + 1) - 1) / 8 + k ≤ H.edgeSet.ncard}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
        Tendsto (fun i => f (m i)) atTop atTop

end Problem
