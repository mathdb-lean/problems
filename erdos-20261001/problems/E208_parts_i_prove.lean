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

- problem_id: E208_parts_i_prove
- collection: erdos
- question_id: erdos:208
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/208.lean#erdos_208.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $s_1 < s_2 < \dots$ be the sequence of squarefree numbers. Is it true that for any $\epsilon > 0$ and large $n$, $s_{n+1} - s_n \ll_\epsilon s_n^\epsilon$?
- notes: Erdos Problem 208 -- https://www.erdosproblems.com/208
- track: open
- answer_shape: prove
- pair_id: E208_parts_i
- pair_role: prove
- source_stem: 208
- mathdb_ref: erdos:208
- source_namespace: Erdos208
- source_theorem: erdos_208.parts.i
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real

namespace Problem

/-- The sequence of squarefree numbers, denoted by `s` as in Erdős problem 208. -/
noncomputable def erdos208.s : ℕ → ℕ := Nat.nth Squarefree

open erdos208

abbrev Target : Prop :=
    ∀ ε > (0 : ℝ), (fun n => (s (n + 1) - s n : ℝ)) =O[atTop] (fun n => (s n : ℝ)^ε)

end Problem
