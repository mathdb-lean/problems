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

- problem_id: E454_prove
- collection: erdos
- question_id: erdos:454
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/454.lean#erdos_454
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that `limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop = ⊤`?
- notes: Erdos Problem 454 -- https://www.erdosproblems.com/454
- track: open
- answer_shape: prove
- pair_id: E454
- pair_role: prove
- source_stem: 454
- mathdb_ref: erdos:454
- source_namespace: Erdos454
- source_theorem: erdos_454
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

/-- Define `f n` to be the minimum of `(n + i).nth Prime + (n - i).nth Prime` over `0 < i < n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else ⨅ i : {i : Fin n // 0 < (i : ℕ)}, (n + i).nth Prime + (n - i).nth Prime

abbrev Target : Prop :=
    limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop = ⊤

end Problem
