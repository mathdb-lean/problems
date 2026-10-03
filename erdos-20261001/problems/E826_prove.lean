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

- problem_id: E826_prove
- collection: erdos
- question_id: erdos:826
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/826.lean#erdos_826
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many $n$ such that, for all $k\geq 1$ $$ \tau(n + k) \ll k? $$
- notes: Erdos Problem 826 -- https://www.erdosproblems.com/826
- track: open
- answer_shape: prove
- pair_id: E826
- pair_role: prove
- source_stem: 826
- mathdb_ref: erdos:826
- source_namespace: Erdos826
- source_theorem: erdos_826
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped ArithmeticFunction.sigma

namespace Problem

abbrev Target : Prop :=
    ∃ C > (0 : ℝ), { n | ∀ k ≥ 1, σ 0 (n + k) ≤ C * k }.Infinite

end Problem
