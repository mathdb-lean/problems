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

- problem_id: E582
- collection: erdos
- question_id: erdos:582
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/582.lean#erdos_582
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist a graph $G$ which contains no $K_4$, and yet any $2$-colouring of the edges produces a monochromatic $K_3$? Erdős and Hajnal [ErHa67] first asked for the existence of any such graph. Existence was proved by Folkman [Fo70], but with very poor quantitative bounds. (As a result these quantities are often called Folkman numbers.) The current best bounds on the minimal number of vertices $N$ of such a graph are $21 \leq N \leq 786$, where the lower bound is due to Bikov and Nenov [BiNe20] and the upper bound is due to Lange, Radziszowski, and Xu [LRX14].
- notes: Erdos Problem 582 -- https://www.erdosproblems.com/582
- track: solved
- answer_shape: decide
- source_stem: 582
- mathdb_ref: erdos:582
- source_namespace: Erdos582
- source_theorem: erdos_582
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/--
A graph `G` is *edge-Ramsey for triangles* (in arrow notation, $G \to (K_3, K_3)^e$) if any
$2$-colouring of the edges of `G` produces a monochromatic $K_3$: three pairwise adjacent
vertices whose three connecting edges all receive the same colour.
-/
def EdgeRamseyTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ c : G.edgeSet → Fin 2,
    ∃ (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w),
      c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧ c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ (V : Type*) (_ : Fintype V) (G : SimpleGraph V),
          G.CliqueFree 4 ∧ EdgeRamseyTriangle G

end Problem
