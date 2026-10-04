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

- problem_id: E502
- collection: erdos
- question_id: erdos:502
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/502.lean#erdos_502
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: What is the size of the largest $A\subseteq \mathbb{R}^n$ such that there are only two distinct distances between elements of $A$? That is, $$\# \{ \lvert x-y\rvert : x\neq y\in A\} = 2.$$ Asked to Erdős by Coxeter. Bannai, Bannai, and Stanton [BBS83] have proved that $$\lvert A\rvert \leq \binom{n+2}{2}.$$ A simple proof of this upper bound was given by Petrov and Pohoata [PePo21]. The exact maximum is not known in general: a lower bound of $\binom{n+1}{2}$ follows from the construction of Alweiss (see [503]).
- notes: Erdos Problem 502 -- https://www.erdosproblems.com/502
- track: solved
- answer_shape: proof
- source_stem: 502
- mathdb_ref: erdos:502
- source_namespace: Erdos502
- source_theorem: erdos_502
- source_category: research solved
- source_ams: 51 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped EuclideanGeometry

namespace Problem

abbrev Target : Prop :=
    ∀ (n : ℕ) (A : Set (ℝ^n)) (hA : A.Finite)
        (hA2 : {d : ℝ | ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ dist x y = d}.ncard = 2),
      A.ncard ≤ (n + 2).choose 2

end Problem
