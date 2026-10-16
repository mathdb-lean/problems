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

- problem_id: X2507_17780_3_tx_graffiti_conjecture_3
- collection: arxiv
- question_id: arxiv:2507.17780/3
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/2507.17780/3.lean#tx_graffiti_conjecture_3
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: TxGraffiti [Conjecture 3](https://arxiv.org/abs/2507.17780): for every $r$-regular graph $G$ ($r \ge 1$), $$i(G) \le \mu^*(G).$$ This conjecture is **open**.
- notes: arXiv 2507.17780/3 -- https://arxiv.org/abs/2507.17780
- track: open
- answer_shape: proof
- source_stem: 2507.17780/3
- source_namespace: Arxiv.«2507.17780»
- source_theorem: tx_graffiti_conjecture_3
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph

namespace Problem

abbrev Target : Prop :=
    ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (r : ℕ) (_hReg : ∀ v, G.degree v = r) (_hr : 1 ≤ r),
      G.indepDominationNumber ≤ G.saturationNumber

end Problem
