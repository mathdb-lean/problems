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

- problem_id: E904
- collection: erdos
- question_id: erdos:904
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/904.lean#erdos_904
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $r\geq 2$ and let $t_r(n)$ be the Turán number (the maximal number of edges in a graph on $n$ vertices with no $K_{r+1}$). If $G$ is a graph with $n$ vertices and $m\geq t_r(n)$ edges there exists a clique on $r$ vertices, say $x_1,\ldots,x_r$, such that $$d(x_1)+\cdots+d(x_r)\geq \frac{2rm}{n}.$$ A conjecture of Bollobás and Erdős. This was conjectured in [Er75] only in the special case $r=3$. Edwards [Ed78] proved the conjecture for $2\leq r\leq 8$ (under the additional assumption that $n\geq r^2$). Faudree [Fa92] proved the conjecture for all $r\geq 2$ provided $n>\frac{r-1}{4}r^2$. The full conjecture was proved by Bollobás and Nikiforov [BoNi05].
- notes: Erdos Problem 904 -- https://www.erdosproblems.com/904
- track: solved
- answer_shape: decide
- source_stem: 904
- mathdb_ref: erdos:904
- source_namespace: Erdos904
- source_theorem: erdos_904
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Finset

/-- An abbreviation for the fixed number of vertices $n$ in the graph. -/
abbrev n (V : Type*) [Fintype V] : ℕ := Fintype.card V

/-- The number of edges of the Turán graph $T(n, r)$, i.e. the Turán number. -/
abbrev turanNumber (n r : ℕ) : ℕ := #(SimpleGraph.turanGraph n r).edgeFinset

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (r : ℕ) (hr : r ∈ Set.Icc 1 (n V)) (hm : turanNumber (n V) r ≤ #G.edgeFinset),
      ∃ s, G.IsNClique r s ∧ 2 * r * #G.edgeFinset ≤ n V * ∑ v ∈ s, G.degree v

end Problem
