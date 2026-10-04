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

- problem_id: E850_prove
- collection: erdos
- question_id: erdos:850
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/850.lean#erdos_850
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Can there exist two distinct integers $x$ and $y$ such that $x,y$ have the same prime factors, $x+1,y+1$ have the same prime factors, and $x+2,y+2$ also have the same prime factors?
- notes: Erdos Problem 850 -- https://www.erdosproblems.com/850
- track: open
- answer_shape: prove
- pair_id: E850
- pair_role: prove
- source_stem: 850
- mathdb_ref: erdos:850
- source_namespace: Erdos850
- source_theorem: erdos_850
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∃ x y : ℕ, x ≠ y ∧ x.primeFactors = y.primeFactors
      ∧ (x + 1).primeFactors = (y + 1).primeFactors
      ∧ (x + 2).primeFactors = (y + 2).primeFactors

end Problem
