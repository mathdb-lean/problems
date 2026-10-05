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

- problem_id: WGraphConjecture18_conjecture18
- collection: wotw
- question_id: wotw:GraphConjecture18
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture18.lean#conjecture18
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 18](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph $G$, the size $b(G)$ of a largest induced bipartite subgraph satisfies $b(G) \ge \alpha(G) + \lceil \sqrt{\mathrm{dist}_{\max}(M)} \rceil$, where $\alpha(G)$ is the independence number, $M$ is the set of maximum-degree vertices, and $\mathrm{dist}_{\max}(M) = \max\{\mathrm{dist}_G(u,v) \mid u, v \in M\}$ is the maximum distance between two maximum-degree vertices (DeLaVina's `dist_max(M)`). Proven by Benny John (Feb. 2006), generalizing Schindl's proof of conjecture 17.
- notes: Written on the Wall II, problem GraphConjecture18 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture18
- source_namespace: WrittenOnTheWallII.GraphConjecture18
- source_theorem: conjecture18
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let M : Set α := {v | G.degree v = G.maxDegree}
      (G.indepNum : ℝ) + ⌈Real.sqrt (distMaxSet G M : ℝ)⌉ ≤ b G

end Problem
