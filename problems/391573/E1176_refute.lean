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

- problem_id: E1176_refute
- collection: erdos
- question_id: erdos:1176
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1176.lean#erdos_1176
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph with chromatic number $\aleph_1$. Is it true that there is a colouring of the edges with $\aleph_1$ many colours such that, in any countable colouring of the vertices, there exists a vertex colour containing all edge colours? A problem of Erdős, Galvin, and Hajnal. The consistency of this was proved by Hajnal and Komjáth.
- notes: Erdos Problem 1176 -- https://www.erdosproblems.com/1176
- track: open
- answer_shape: refute
- pair_id: E1176
- pair_role: refute
- source_stem: 1176
- mathdb_ref: erdos:1176
- source_namespace: Erdos1176
- source_theorem: erdos_1176
- source_category: research open
- source_ams: 3 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Cardinal

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ {V : Type*} (G : SimpleGraph V), G.chromaticCardinal = aleph 1 →
        ∃ (EColor : Type) (_ : mk EColor = aleph 1) (c_edge : G.edgeSet → EColor),
          ∀ (VColor : Type) (_ : mk VColor ≤ aleph 0) (c_vert : V → VColor),
            ∃ (vc : VColor),
              ∀ (ec : EColor), ∃ (u v : V) (h : G.Adj u v),
                c_vert u = vc ∧ c_vert v = vc ∧ c_edge ⟨s(u, v), h⟩ = ec
    )

end Problem
