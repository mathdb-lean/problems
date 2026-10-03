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

- problem_id: E545_refute
- collection: erdos
- question_id: erdos:545
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/545.lean#erdos_545
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $m$ be sufficiently large and let $G$ be a graph with $m$ edges and no isolated vertices. Is the Ramsey number $R(G)$ maximised when $G$ is 'as complete as possible'? That is, if $m=\binom{n}{2}+t$ edges with $0\leq t < n$ then is $$R(G)\leq R(H),$$ where $H$ is the graph formed by connecting a new vertex to $t$ of the vertices of $K_n$? A question of Erdős and Graham. The restriction to sufficiently large $m$ excludes the small counterexamples recorded on the source page. This problem is #10 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 545 -- https://www.erdosproblems.com/545
- track: open
- answer_shape: refute
- pair_id: E545
- pair_role: refute
- source_stem: 545
- mathdb_ref: erdos:545
- source_namespace: Erdos545
- source_theorem: erdos_545
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

/--
The graph formed by connecting a new vertex (`none`) to $t$ of the vertices of $K_n$ (`Fin n`).
-/
def knPlusTEdges (n t : ℕ) : SimpleGraph (Option (Fin n)) where
  Adj u v := match u, v with
    | some x, some y => x ≠ y
    | none, some y => y.val < t
    | some x, none => x.val < t
    | none, none => False
  symm.symm u v := by
    cases u <;> cases v <;> simp [ne_comm]
  loopless.irrefl u := by
    cases u <;> simp

abbrev Target : Prop :=
    ¬ (
      ∀ᶠ m : ℕ in atTop, ∀ (n t : ℕ), t < n → m = n.choose 2 + t →
            ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
              (∀ v, 0 < G.degree v) →
              G.edgeSet.ncard = m →
              SimpleGraph.diagonalGraphRamsey G ≤
                SimpleGraph.diagonalGraphRamsey (knPlusTEdges n t)
    )

end Problem
