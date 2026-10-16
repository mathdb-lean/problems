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

- problem_id: G24
- collection: green
- question_id: green:24
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/24.lean#green_24
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $A$ is a set of $n$ integers, what is the maximum number of affine translates of the set $\lbrace 0,1,3 \rbrace$ that $A$ can contain? Conjectured in [Aa19] p.579: $\left(\frac{1}{3} + o(1)\right) n^2$.
- notes: Green, open problem 24 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.24
- track: open
- answer_shape: value
- answer_type: ℕ → ℕ
- answer_pinned: false
- answer_pinned_reason: closable_by_rfl
- source_stem: 24
- source_namespace: Green24
- source_theorem: green_24
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

/--
The maximum number of $\lbrace 0,1,3 \rbrace$ affine translates that a set of size $n$ can
contain.
-/
noncomputable def max013AffineTranslates (n : ℕ) : ℕ :=
  sSup { k |
    ∃ A : Finset ℤ,
      A.card = n ∧
      -- Iterate over (x,y) = (a, a + d) in A × A (x ≠ y), and check if a + 3d = x + 3(y - x) ∈ A
      k = ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card
  }

namespace variants

/-- The asymptotic constant $\gamma$ defined in [Aa19] p.579. -/
noncomputable def gamma : ℝ :=
  limsup (fun n : ℕ => (max013AffineTranslates n : ℝ) / ((n : ℝ)^2)) atTop

end variants

abbrev Target (value : ℕ → ℕ) : Prop :=
    ∀ n, max013AffineTranslates n = value n

end Problem
