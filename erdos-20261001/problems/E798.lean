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

- problem_id: E798
- collection: erdos
- question_id: erdos:798
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/798.lean#erdos_798
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $t(n)$ be the minimum number of points in $\{1,\ldots,n\}^2$ such that the $\binom{t}{2}$ lines determined by these points cover all points in $\{1,\ldots,n\}^2$. Estimate $t(n)$. In particular, is it true that $t(n)=o(n)$? A problem of Erdős and Purdy, who proved $t(n) \gg n^{2/3}$. Resolved by Alon [Al91] who proved $t(n) \ll n^{2/3}\log n$.
- notes: Erdos Problem 798 -- https://www.erdosproblems.com/798
- track: solved
- answer_shape: decide
- source_stem: 798
- mathdb_ref: erdos:798
- source_namespace: Erdos798
- source_theorem: erdos_798
- source_category: research solved
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Filter Asymptotics

/--
The grid $\{1,\ldots,n\}^2$, viewed as a set of points of the plane.
-/
def gridPoints (n : ℕ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | ∃ i j : ℕ, 1 ≤ i ∧ i ≤ n ∧ 1 ≤ j ∧ j ≤ n ∧ p = ((i : ℝ), (j : ℝ))}

/--
`S` is a set of points of $\{1,\ldots,n\}^2$ such that the lines determined by the pairs of
distinct points of `S` cover all points of $\{1,\ldots,n\}^2$.
-/
def IsLineCover (n : ℕ) (S : Set (ℝ × ℝ)) : Prop :=
  S ⊆ gridPoints n ∧
    ∀ x ∈ gridPoints n, ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ Collinear ℝ ({p, q, x} : Set (ℝ × ℝ))

/--
The minimum number of points in $\{1,\ldots,n\}^2$ such that the lines determined by these points
cover all points in $\{1,\ldots,n\}^2$.
-/
noncomputable def t (n : ℕ) : ℕ :=
  sInf {k | ∃ S : Set (ℝ × ℝ), IsLineCover n S ∧ S.ncard = k}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        (fun n : ℕ => (t n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ))

end Problem
