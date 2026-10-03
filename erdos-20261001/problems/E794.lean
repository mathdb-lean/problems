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

- problem_id: E794
- collection: erdos
- question_id: erdos:794
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/794.lean#erdos_794
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that every $3$-uniform hypergraph on $3n$ vertices with at least $n^3+1$ edges must contain either a subgraph on $4$ vertices with $3$ edges or a subgraph on $5$ vertices with $7$ edges? Harris has provided the following simple counterexample to the problem as stated: the $3$-uniform graph on $\{1,\ldots,9\}$ with $28$ edges, formed by taking $27$ edges by choosing one element each from $\{1,2,3\},\{4,5,6\},\{7,8,9\}$, and then adding the edge $\{1,2,3\}$.
- notes: Erdos Problem 794 -- https://www.erdosproblems.com/794
- track: solved
- answer_shape: decide
- source_stem: 794
- mathdb_ref: erdos:794
- source_namespace: Erdos794
- source_theorem: erdos_794
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

/-- The `3`-uniform hypergraph on `Fin 9` given by Harris: the `27` triples containing exactly
one vertex from each of the three parts `{0, 1, 2}`, `{3, 4, 5}`, `{6, 7, 8}`, together with the
triple `{0, 1, 2}`. A triple is a transversal of the three parts exactly when the three values
of `v ↦ v / 3` it produces are distinct. -/
def harrisHypergraph : Finset (Finset (Fin 9)) :=
  insert {0, 1, 2}
    (Finset.filter
      (fun e : Finset (Fin 9) =>
        (Finset.image (fun v : Fin 9 => (v : ℕ) / 3) e).card = 3)
      (Finset.powersetCard 3 Finset.univ))

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ n : ℕ, ∀ H : Finset (Finset (Fin (3 * n))), H.IsThreeUniform →
          n ^ 3 + 1 ≤ H.card → H.ContainsSubgraph 4 3 ∨ H.ContainsSubgraph 5 7

end Problem
