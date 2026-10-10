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

- problem_id: E75_prove
- collection: erdos
- question_id: erdos:75
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/75.lean#erdos_75
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a graph of chromatic number `ℵ_ 1` with `ℵ_ 1` vertices such that for all `ε > 0`, if `n` is sufficiently large and `H` is a subgraph on `n` vertices, then `H` contains an independent set of size `> n ^ (1 - ε)`?
- notes: Erdos Problem 75 -- https://www.erdosproblems.com/75
- track: open
- answer_shape: prove
- pair_id: E75
- pair_role: prove
- source_stem: 75
- mathdb_ref: erdos:75
- source_namespace: Erdos75
- source_theorem: erdos_75
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Cardinal

namespace Problem

abbrev Target : Prop :=
    ∃ (V : Type) (G : SimpleGraph V),
      G.chromaticCardinal = ℵ_ 1 ∧
      #V = ℵ_ 1 ∧
      ∀ ε > (0 : ℝ),
        ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (H : G.Subgraph),
            H.verts.ncard = n →
            ∃ (I : Finset V),
              (I : Set V) ⊆ H.verts ∧
              G.IsIndepSet (I : Set V) ∧
              (I.card : ℝ) > (n : ℝ) ^ (1 - ε)

end Problem
