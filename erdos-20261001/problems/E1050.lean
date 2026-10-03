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

- problem_id: E1050
- collection: erdos
- question_id: erdos:1050
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1050.lean#erdos_1050
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 1050.** The series $\sum_{n=1}^\infty \frac{1}{2^n - 3}$ is irrational. The source sum runs over $n \ge 1$; as a `tsum` over `ℕ` (which starts at $0$) it is reindexed $n \mapsto n + 1$, i.e. $\sum_{n=0}^\infty 1/(2^{n+1} - 3)$.
- notes: Erdos Problem 1050 -- https://www.erdosproblems.com/1050
- track: solved
- answer_shape: proof
- source_stem: 1050
- mathdb_ref: erdos:1050
- source_namespace: Erdos1050
- source_theorem: erdos_1050
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3))

end Problem
