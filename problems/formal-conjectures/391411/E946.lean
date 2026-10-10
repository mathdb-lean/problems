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

- problem_id: E946
- collection: erdos
- question_id: erdos:946
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/946.lean#erdos_946
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There are infinitely many $n$ such that $τ(n) = τ(n+1)$. Proved in [He84]. Here τ is the divisor counting function, which is `σ 0` in mathlib.
- notes: Erdos Problem 946 -- https://www.erdosproblems.com/946
- track: solved
- answer_shape: proof
- source_stem: 946
- mathdb_ref: erdos:946
- source_namespace: Erdos946
- source_theorem: erdos_946
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real
open scoped ArithmeticFunction.sigma

namespace Problem

/-- Number of $n \le x$ with $τ(n) = τ(n+1)$. -/
noncomputable def erdos946Count (x : ℝ) : ℝ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter (fun n => σ 0 n = σ 0 (n + 1))).card

abbrev Target : Prop :=
    {n : ℕ | σ 0 n = σ 0 (n + 1)}.Infinite

end Problem
