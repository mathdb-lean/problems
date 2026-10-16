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

- problem_id: G41
- collection: green
- question_id: green:41
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/41.lean#green_41
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: How many rotated (about the origin) copies of the 'pyjama set' $\\{(x, y) \in \mathbb{R}^2 : \text{dist}(x, \mathbb{Z}) \leq \varepsilon\\}$ are needed to cover $\mathbb{R}^2$? That is, determine the minimal number of rotations as a function of $\varepsilon > 0$.
- notes: Green, open problem 41 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.41
- track: open
- answer_shape: value
- answer_type: ℝ → ℕ
- answer_pinned: false
- answer_pinned_reason: closable_by_rfl
- source_stem: 41
- source_namespace: Green41
- source_theorem: green_41
- source_category: research open
- source_ams: 51 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Complex Set Pointwise

/--
The pyjama set is the set of points in the complex plane whose real part is within $\varepsilon$ of
an integer.
-/
def pyjamaSet (ε : ℝ) : Set ℂ :=
  { z | ∃ k : ℤ, |z.re - (k : ℝ)| ≤ ε }

/-- The set of valid numbers of rotated copies of the pyjama set of width ε that cover the plane. -/
def coveringCopies (ε : ℝ) : Set ℕ :=
  { n : ℕ | ∃ (Θ : Finset ℝ), Θ.card = n ∧
    (⋃ θ ∈ Θ, exp (θ * I) • pyjamaSet ε) = univ }

/-- The minimal number of rotated copies of the pyjama set of width ε needed to cover the plane. -/
noncomputable def minCopies (ε : ℝ) : ℕ :=
  sInf (coveringCopies ε)

abbrev Target (value : ℝ → ℕ) : Prop :=
    ∀ ε > 0, minCopies ε = value ε

end Problem
