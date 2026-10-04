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

- problem_id: E416_parts_i
- collection: erdos
- question_id: erdos:416
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/416.lean#erdos_416.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable. Does `V(2x)/V(x)→2` ?
- notes: Erdos Problem 416 -- https://www.erdosproblems.com/416
- track: open
- answer_shape: proof
- source_stem: 416
- mathdb_ref: erdos:416
- source_namespace: Erdos416
- source_theorem: erdos_416.parts.i
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped Topology Real

namespace Problem

/-- Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable. -/
noncomputable abbrev V (x : ℝ) : ℝ :=
  open scoped Classical in
  (Finset.Icc 1 ⌊x⌋₊ |>.filter (fun n => ∃ (m : ℕ), m.totient = n)).card

abbrev Target : Prop :=
    Filter.Tendsto (fun x => (V (2 * x) / V (x))) Filter.atTop (𝓝 2)

end Problem
