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

- problem_id: E779
- collection: erdos
- question_id: erdos:779
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/779.lean#erdos_779
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: A Conjecture of Marian Deaconescu, see p.120 in https://doi.org/10.2307/2975810 [Needed to index shift in order to avoid trivial case $n = 0$, where the conjecture is trivially false.]
- notes: Erdos Problem 779 -- https://www.erdosproblems.com/779
- track: open
- answer_shape: proof
- source_stem: 779
- mathdb_ref: erdos:779
- source_namespace: Erdos779
- source_theorem: erdos_779
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset Nat

namespace Problem

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : n ≥ 1),
      let P := ∏ i ∈ range (n + 1), nth Nat.Prime i
          ∃ p, p.Prime ∧ (P + p).Prime ∧ nth Nat.Prime n < p ∧ p < P

end Problem
