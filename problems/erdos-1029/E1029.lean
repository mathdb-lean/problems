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

- problem_id: E1029
- collection: erdos
- question_id: erdos:1029
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1029.lean#erdos_1029
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $R(k)$ is the Ramsey number for $K_k$, the minimal $n$ such that every $2$-colouring of the edges of $K_n$ contains a monochromatic copy of $K_k$, then $$\frac{R(k)}{k2^{k/2}}\to \infty.$$ In [Er93] Erdős offers $100 for a proof of this and $1000 for a disproof, but says 'this last offer is to some extent phoney: I am sure that this is true (but I have been wrong before).'
- notes: Erdos Problem 1029 -- https://www.erdosproblems.com/1029
- track: open
- answer_shape: proof
- source_stem: 1029
- mathdb_ref: erdos:1029
- source_namespace: Erdos1029
- source_theorem: erdos_1029
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    Tendsto (fun k : ℕ ↦ (SimpleGraph.diagonalRamsey k : ℝ) /
      ((k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2))) atTop atTop

end Problem
