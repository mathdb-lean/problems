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

- problem_id: NVizingConjecture_vizing_conjecture_refute
- collection: wikipedia
- question_id: wikipedia:VizingConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/VizingConjecture.lean#vizing_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Vizing's conjecture (1968).** For all finite simple graphs $G$ and $H$, the domination number of the Cartesian (box) product satisfies $\gamma(G \,\square\, H) \ge \gamma(G)\,\gamma(H)$.
- notes: Wikipedia: VizingConjecture -- https://en.wikipedia.org/wiki/Vizing%27s_conjecture
- track: open
- answer_shape: refute
- pair_id: NVizingConjecture_vizing_conjecture
- pair_role: refute
- source_stem: VizingConjecture
- source_namespace: VizingConjecture
- source_theorem: vizing_conjecture
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
            (G : SimpleGraph α) (H : SimpleGraph β),
            G.dominationNumber * H.dominationNumber ≤ (G □ H).dominationNumber
    )

end Problem
