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

- problem_id: E23_refute
- collection: erdos
- question_id: erdos:23
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/23.lean#erdos_23
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges?
- notes: Erdos Problem 23 -- https://www.erdosproblems.com/23
- track: open
- answer_shape: refute
- pair_id: E23
- pair_role: refute
- source_stem: 23
- mathdb_ref: erdos:23
- source_namespace: Erdos23
- source_theorem: erdos_23
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph BigOperators

namespace Problem

/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

open scoped Classical in
abbrev Target : Prop :=
    ¬ (
      ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
            ∀ (G : SimpleGraph V), G.CliqueFree 3 →
              ∃ (H : SimpleGraph V),
                H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n^2
    )

end Problem
