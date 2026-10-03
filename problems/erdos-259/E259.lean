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

- problem_id: E259
- collection: erdos
- question_id: erdos:259
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/259.lean#erdos_259
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is $\sum_{n} \mu(n)^2\frac{n}{2^n}$ irrational? This is true, and was proved by Chen and Ruzsa. [ChRu99] Chen, Yong-Gao and Ruzsa, Imre Z., On the irrationality of certain series. Period. Math. Hungar. (1999), 31--37.
- notes: Erdos Problem 259 -- https://www.erdosproblems.com/259
- track: solved
- answer_shape: proof
- source_stem: 259
- mathdb_ref: erdos:259
- source_namespace: Erdos259
- source_theorem: erdos_259
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped ArithmeticFunction.Moebius

namespace Problem

abbrev Target : Prop :=
    Irrational (∑' n : ℕ, (μ n) ^ 2 * n / (2 ^ n))

end Problem
