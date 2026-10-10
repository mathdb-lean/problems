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

- problem_id: E266
- collection: erdos
- question_id: erdos:266
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/266.lean#erdos_266
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a_n$ be an infinite sequence of positive integers such that $\sum \frac{1}{a_n}$ converges. There exists some integer $t \ge 1$ such that $\sum \frac{1}{a_n + t}$ is irrational. This was disproven by Kovač and Tao in [KoTa24]. [KoTa24] Kovač, V. and Tao T., On several irrationality problems for Ahmes series. [arXiv:2406.17593](https://arxiv.org/abs/2406.17593) (2024).
- notes: Erdos Problem 266 -- https://www.erdosproblems.com/266
- track: solved
- answer_shape: proof
- source_stem: 266
- mathdb_ref: erdos:266
- source_namespace: Erdos266
- source_theorem: erdos_266
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter

abbrev Target : Prop :=
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·) →
      ∃ t ≥ (1 : ℕ), Irrational <| ∑' n, (1 : ℝ) / ((a n) + t))

end Problem
