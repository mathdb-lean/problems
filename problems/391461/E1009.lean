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

- problem_id: E1009
- collection: erdos
- question_id: erdos:1009
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1009.lean#erdos_1009
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for every $c>0$, there exists $f(c)$ such that every graph on $n$ vertices with at least $\lfloor n^2/4\rfloor+k$ edges, where $k<c n$, contains at least $k-f(c)$ many edge disjoint triangles? Erdős [Er71] proved this for $c<1/2$ using a theorem of Erdős and Gallai, which says that every graph on $n$ vertices with at least $(n-1)^2/4+2$ many edges, with chromatic number $3$, must contain a triangle. In fact, Erdős proved this is true with $f(c)=0$ for $c<1/2$. At first Erdős thought $f(c)=0$ for larger values of $c$ but this is false: an example of Sauer proves that $f(2)\geq 1$. This is true, and was proved by Győri [Gy88] who proved that this is true with $f(c)\ll c^2$, and also that $f(c)=0$ if $c<2$ for odd $n$ or $c<3/2$ for even $n$. A family of edge disjoint triangles is a finite set of $3$-cliques of $G$ any two of which share at most one vertex.
- notes: Erdos Problem 1009 -- https://www.erdosproblems.com/1009
- track: solved
- answer_shape: decide
- source_stem: 1009
- mathdb_ref: erdos:1009
- source_namespace: Erdos1009
- source_theorem: erdos_1009
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ c : ℝ, 0 < c → ∃ f : ℕ, ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
        n ^ 2 / 4 + k ≤ G.edgeSet.ncard → (k : ℝ) < c * n →
          ∃ T : Finset (Finset (Fin n)), (∀ t ∈ T, G.IsNClique 3 t) ∧
            (T : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ k ≤ T.card + f

end Problem
