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

- problem_id: E947
- collection: erdos
- question_id: erdos:947
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/947.lean#erdos_947
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There is no exact covering system - that is, a finite collection of congruence classes $a_i\pmod{n_i}$ with distinct $n_i$ such that every integer satisfies exactly one of these congruence classes. This is true, and was proved independently by Mirsky and Newman and by Davenport and Rado; the Mirsky–Newman proof first appeared in [Er50]. See also [Er77c]. A `StrictCoveringSystem ℤ` is a finite family of congruence classes with distinct moduli $n_i \geq 2$ covering $\mathbb{Z}$; the trivial exact covering system consisting of the single class $0 \pmod 1$ is therefore excluded.
- notes: Erdos Problem 947 -- https://www.erdosproblems.com/947
- track: solved
- answer_shape: proof
- source_stem: 947
- mathdb_ref: erdos:947
- source_namespace: Erdos947
- source_theorem: erdos_947
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Function

namespace Problem

abbrev Target : Prop :=
    ¬ ∃ c : StrictCoveringSystem ℤ, Pairwise (Disjoint on c.coset)

end Problem
