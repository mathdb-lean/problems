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

- problem_id: E968_prove
- collection: erdos
- question_id: erdos:968
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/968.lean#erdos_968
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does the set `{n | u n < u (n+1)}` have positive lower density?
- notes: Erdos Problem 968 -- https://www.erdosproblems.com/968
- track: open
- answer_shape: prove
- pair_id: E968
- pair_role: prove
- source_stem: 968
- mathdb_ref: erdos:968
- source_namespace: Erdos968
- source_theorem: erdos_968
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real
open scoped BigOperators

namespace Problem

/--
`u n` is the normalized `n`th prime, defined as `pₙ / (n+1)` where `pₙ` is the `n`th prime
(with `0.nth Nat.Prime = 2`).

This corresponds to the classical sequence `(p₁/1, p₂/2, p₃/3, ...)` while using `Nat.nth Prime`'s
`0`-based indexing; in particular, the denominator is always positive.
-/
noncomputable def u (n : ℕ) : ℝ :=
  (n.nth Nat.Prime : ℝ) / (n + 1)

abbrev Target : Prop :=
    0 < {n : ℕ | u n < u (n + 1)}.lowerDensity

end Problem
