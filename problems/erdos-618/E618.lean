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

- problem_id: E618
- collection: erdos
- question_id: erdos:618
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/618.lean#erdos_618
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For a triangle-free graph $G$ let $h_2(G)$ be the smallest number of edges that need to be added to $G$ so that it has diameter $2$ and is still triangle-free. Is it true that if $G$ has maximum degree $o(n^{1/2})$ then $h(G)=o(n^2)$? A problem of Erdős, Gyárfás, and Ruszinkó [EGR98]. Simonovits showed that there exist graphs $G$ with maximum degree $\gg n^{1/2}$ and $h_2(G)\gg n^2$. Alon has observed this problem is essentially identical to [134], and his solution in [this note](https://web.math.princeton.edu/~nalon/PDFS/remark1901.pdf) also solves this problem in the affirmative.
- notes: Erdos Problem 618 -- https://www.erdosproblems.com/618
- track: solved
- answer_shape: decide
- source_stem: 618
- mathdb_ref: erdos:618
- source_namespace: Erdos618
- source_theorem: erdos_618
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Filter Asymptotics

open scoped Classical in
/-- For a graph `G` on `Fin n`, `h2 G` is the smallest number of edges that need to be added
to `G` so that the resulting supergraph has diameter at most `2` (every two distinct vertices
are adjacent or have a common neighbour) and is still triangle-free (`CliqueFree 3`).
By the `sInf` convention on `ℕ`, `h2 G = 0` if no such supergraph exists. -/
noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n),
    G ≤ H ∧
    H.CliqueFree 3 ∧
    (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (G : ∀ n : ℕ, SimpleGraph (Fin n)),
          (∀ n, (G n).CliqueFree 3) →
          (fun n => ((G n).maxDegree : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ ((1 : ℝ) / 2)) →
          (fun n => (h2 (G n) : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2)

end Problem
