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

- problem_id: E1079
- collection: erdos
- question_id: erdos:1079
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1079.lean#erdos_1079
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $r\geq 4$. If $G$ is a graph on $n$ vertices with at least $\mathrm{ex}(n;K_r)$ edges then must $G$ contain a vertex with degree $d\gg_r n$ whose neighbourhood contains at least $\mathrm{ex}(d;K_{r-1})$ edges? As Erdős [Er75] says 'if true this would be a nice generalisation of Turán's theorem'. This is true (unless $G$ it itself the Turán graph), and was proved by Bollobás and Thomason [BoTh81]. Bondy [Bo83b] showed that if $G$ has $>\mathrm{ex}(n;K_r)$ edges then the corresponding vertex can be chosen to be of maximum degree in $G$. The number of edges in the neighbourhood of $v$ is the number of edges of $G$ both of whose endpoints are adjacent to $v$. Graphs on a single vertex are excluded, since there every degree is $0$.
- notes: Erdos Problem 1079 -- https://www.erdosproblems.com/1079
- track: solved
- answer_shape: decide
- source_stem: 1079
- mathdb_ref: erdos:1079
- source_namespace: Erdos1079
- source_theorem: erdos_1079
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ r : ℕ, 4 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
        ∀ G : SimpleGraph (Fin n), extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard →
          ∃ v : Fin n, c * n ≤ G.degree v ∧
            extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) ≤
              {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

end Problem
