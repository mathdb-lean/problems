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

- problem_id: WGraphConjecture109_conjecture109
- collection: wotw
- question_id: wotw:GraphConjecture109
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture109.lean#conjecture109
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 109](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph $G$, the independence number $\alpha(G)$ was conjectured to satisfy $\alpha(G) \le \lfloor (\mathrm{residue}(G) + 2 \cdot b(G)) / 3 \rfloor$, where $\mathrm{residue}(G)$ is the Havel--Hakimi residue and $b(G)$ is the size of a largest induced bipartite subgraph. This is false. A connected graph on 21 vertices has an independent set of size 15, residue 8, and no induced bipartite subgraph with more than 18 vertices, so the conjectured right-hand side is at most 14. A smaller counterexample is the connected 13-vertex graph $\overline K_7 \vee (K_3 \sqcup K_3)$. It has independence number $7$, residue $2$, and largest induced bipartite subgraph size $9$, so its conjectured right-hand side is $6$.
- notes: Written on the Wall II, problem GraphConjecture109
- track: solved
- answer_shape: decide
- source_stem: GraphConjecture109
- source_namespace: WrittenOnTheWallII.GraphConjecture109
- source_theorem: conjecture109
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
          (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected),
          (G.indepNum : ℝ) ≤ ⌊((residue G : ℝ) + 2 * b G) / 3⌋

end Problem
