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

- problem_id: E108_refute
- collection: erdos
- question_id: erdos:108
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/108.lean#erdos_108
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For every r ≥ 4 and k ≥ 2 is there some finite f(k,r) such that every graph of chromatic number ≥ f(k,r) contains a subgraph of girth ≥ r and chromatic number ≥ k?
- notes: Erdos Problem 108 -- https://www.erdosproblems.com/108
- track: open
- answer_shape: refute
- pair_id: E108
- pair_role: refute
- source_stem: 108
- mathdb_ref: erdos:108
- source_namespace: Erdos108
- source_theorem: erdos_108
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

universe u

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ r ≥ 4, ∀ k ≥ (2 : ℕ), ∃ (f : ℕ),
      ∀ (V : Type u) (G : SimpleGraph V) (_ : Nonempty V)
        (hchro : f ≤ SimpleGraph.chromaticNumber G),
      ∃ (H : G.Subgraph), (SimpleGraph.girth H.coe ≥ r) ∧
      (SimpleGraph.chromaticNumber H.coe ≥ k)
    )

end Problem
