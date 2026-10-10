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

- problem_id: E438
- collection: erdos
- question_id: erdos:438
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/438.lean#erdos_438
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: How large can $A \subseteq \{1, \ldots, N\}$ be if $A + A$ contains no square numbers? A problem of Erdős [Er80, Er80c, ErGr80]. Taking all integers $\equiv 1 \pmod 3$ gives $|A| \ge N/3$, and Massias observed that all integers $\equiv 1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30 \pmod{32}$ give $|A| \ge \frac{11}{32} N$. Lagarias, Odlyzko and Shearer [LOS83] proved that $11/32$ is sharp for the modular version of the problem, and Khalfalah, Lodha and Szemerédi [KLS02] proved that it is sharp in general: the maximal such $A$ satisfies $|A| \le (\frac{11}{32} + o(1)) N$.
- notes: Erdos Problem 438 -- https://www.erdosproblems.com/438
- track: solved
- answer_shape: proof
- source_stem: 438
- mathdb_ref: erdos:438
- source_namespace: Erdos438
- source_theorem: erdos_438
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped Topology

namespace Problem

/-- A finite set of natural numbers is square-sum-free if the sum of any two of its elements
(possibly equal) is not a square. -/
def SquareSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ IsSquare (a + b)

/-- The largest size of a square-sum-free subset of `{1, …, N}`. -/
noncomputable def extremalSize (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).powerset.filter SquareSumFree).sup Finset.card

abbrev Target : Prop :=
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop (𝓝 ((11 : ℝ) / 32))

end Problem
