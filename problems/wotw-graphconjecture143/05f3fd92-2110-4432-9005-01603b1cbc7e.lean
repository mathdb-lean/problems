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

- problem_id: WGraphConjecture143_conjecture143
- collection: wotw
- question_id: wotw:GraphConjecture143
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture143.lean#conjecture143
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 143](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj143): For a simple connected graph $G$, $\mathrm{tree}(G) \ge (\mathrm{girth}(G) + 1) / \sigma(G)$, where $\mathrm{tree}(G)$ is the largest induced tree size, $\mathrm{girth}(G)$ is the length of the shortest cycle, and $\sigma(G) = G.\mathrm{secondSmallestDegree}$ is the **second-smallest degree** of $G$'s degree sequence (per WOWII defEntry 65). We state the inequality in denominator-free form to avoid the $\sigma = 0$ corner case ($n \le 1$). The proof splits into the acyclic case and two cyclic cases. For an acyclic graph the girth is zero. If $\sigma \ge 2$, deleting two consecutive edges from a shortest cycle leaves an induced tree on $\mathrm{girth}(G)-1$ vertices, and the factor $\sigma \ge 2$ yields the required inequality. If $\sigma = 1$, there are two degree-one vertices. A maximal induced tree containing them must have an external vertex with two attachments; those attachments create a cycle whose length forces the tree to contain at least $\mathrm{girth}(G)+1$ vertices.
- notes: Written on the Wall II, problem GraphConjecture143
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture143
- source_namespace: WrittenOnTheWallII.GraphConjecture143
- source_theorem: conjecture143
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
        (hσ : 0 < secondSmallestDegree G),
      (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ)

end Problem
