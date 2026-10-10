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

- problem_id: E409_parts_ii_prove
- collection: erdos
- question_id: erdos:409
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/409.lean#erdos_409.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Can infinitely many $n$ reach the same prime under the iteration $n\mapsto\phi(n) + 1$?
- notes: Erdos Problem 409 -- https://www.erdosproblems.com/409
- track: open
- answer_shape: prove
- pair_id: E409_parts_ii
- pair_role: prove
- source_stem: 409
- mathdb_ref: erdos:409
- source_namespace: Erdos409
- source_theorem: erdos_409.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Topology ArithmeticFunction.sigma Nat
open Filter

namespace Problem

abbrev Target : Prop :=
    ∃ (p : ℕ) (hp : p.Prime), { n | ∃ i, (φ · + 1)^[i] n = p }.Infinite

end Problem

-- Formalisation note: the sequence of iterates always terminates if `n > 0`

-- Formalisation note: it's possible that solution to `erdos_409.parts.i` needs to be

-- Formalisation note: termination of this sequence is not known in general since

-- Formalisation note: See the above formalisation note for the rationale
