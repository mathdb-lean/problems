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

- problem_id: E803
- collection: erdos
- question_id: erdos:803
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/803.lean#erdos_803
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: We call a graph $H$ $D$-balanced (or $D$-almost-regular) if the maximum degree of $H$ is at most $D$ times the minimum degree of $H$. Is it true that for every $m\geq 1$, if $n$ is sufficiently large, any graph on $n$ vertices with $\geq n\log n$ edges contains a $O(1)$-balanced subgraph with $m$ vertices and $\gg m\log m$ edges (where the implied constants are absolute)? A problem of Erdős and Simonovits [ErSi70]. Alon [Al08] proved this is false: for every $D>1$ and large $n$ there is a graph $G$ with $n$ vertices and $\geq n\log n$ edges such that if $H$ is a $D$-balanced subgraph then $H$ has $\ll m\sqrt{\log m}+\log D$ many edges. See also [1077](https://www.erdosproblems.com/1077).
- notes: Erdos Problem 803 -- https://www.erdosproblems.com/803
- track: solved
- answer_shape: decide
- source_stem: 803
- mathdb_ref: erdos:803
- source_namespace: Erdos803
- source_theorem: erdos_803
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Real SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ (D c : ℝ), 0 < c ∧ ∀ m ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
          (n : ℝ) * log n ≤ G.edgeSet.ncard →
            ∃ H : G.Subgraph, H.verts.ncard = m ∧ IsBalanced H.coe D ∧
              c * m * log m ≤ H.edgeSet.ncard

end Problem
