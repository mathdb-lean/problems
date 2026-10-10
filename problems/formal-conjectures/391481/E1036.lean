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

- problem_id: E1036
- collection: erdos
- question_id: erdos:1036
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1036.lean#erdos_1036
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph on $n$ vertices which does not contain a trivial (empty or complete) graph on more than $c\log n$ vertices. Must $G$ contain at least $2^{\Omega_c(n)}$ many induced subgraphs which are not pairwise isomorphic? This is true, and was proved by Shelah [Sh98].
- notes: Erdos Problem 1036 -- https://www.erdosproblems.com/1036
- track: solved
- answer_shape: decide
- source_stem: 1036
- mathdb_ref: erdos:1036
- source_namespace: Erdos1036
- source_theorem: erdos_1036
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

/--
`G` contains at least `k` many induced subgraphs which are not pairwise isomorphic, that is,
there is a family of at least `k` many sets of vertices whose induced subgraphs are pairwise
non-isomorphic.
-/
def HasManyNonIsomorphicInducedSubgraphs {V : Type*} (G : SimpleGraph V) (k : ℝ) : Prop :=
  ∃ 𝒮 : Set (Set V), (𝒮.Pairwise fun s t => IsEmpty (G.induce s ≃g G.induce t)) ∧
    k ≤ (𝒮.ncard : ℝ)

/--
Neither `G` nor its complement contains a balanced complete bipartite graph $K_{k,k}$ on more
than `m` vertices as a (not necessarily induced) subgraph. That is, there are no two disjoint
sets of `k` vertices with $2k > m$ such that every pair of vertices from different sets is
adjacent in `G`, or every such pair is non-adjacent in `G`.
-/
def NoLargeBiclique {V : Type*} (G : SimpleGraph V) (m : ℝ) : Prop :=
  ∀ k : ℕ, ((completeBipartiteGraph (Fin k) (Fin k)).IsContained G ∨
    (completeBipartiteGraph (Fin k) (Fin k)).IsContained Gᶜ) → (2 * k : ℝ) ≤ m

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
          (G.cliqueNum : ℝ) ≤ c * Real.log (n : ℝ) → (G.indepNum : ℝ) ≤ c * Real.log (n : ℝ) →
            HasManyNonIsomorphicInducedSubgraphs G ((2 : ℝ) ^ (δ * (n : ℝ)))

end Problem
