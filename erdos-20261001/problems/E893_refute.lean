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

- problem_id: E893_refute
- collection: erdos
- question_id: erdos:893
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/893.lean#erdos_893
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does the limit $\lim_{n\to\infty} \frac{f(2n)}{f(n)}$ tend to infinity? (Other finite limits have been ruled out by [KoLu25], see below)
- notes: Erdos Problem 893 -- https://www.erdosproblems.com/893
- track: open
- answer_shape: refute
- pair_id: E893
- pair_role: refute
- source_stem: 893
- mathdb_ref: erdos:893
- source_namespace: Erdos893
- source_theorem: erdos_893
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Finset
open scoped ArithmeticFunction.sigma

namespace Problem

/--
Definition of function $f(n) := \sum_{1\leq k\leq n}\tau(2^k-1)$.
Here $\tau$ is the divisor counting function, which is `σ 0` in mathlib.
-/
def f (n : ℕ) : ℕ :=  ∑ k ∈ Finset.Icc 1 n, σ 0 (2^k - 1)

abbrev Target : Prop :=
    ¬ (
      Tendsto (fun n : ℕ => (f (2 * n) : ℝ) / (f n : ℝ)) atTop atTop
    )

end Problem
