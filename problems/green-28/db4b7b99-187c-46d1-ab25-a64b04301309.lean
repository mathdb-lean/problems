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

- problem_id: G28_refute
- collection: green
- question_id: green:28
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/28.lean#green_28
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that $X, Y$ are two finitely-supported independent random variables taking integer values, and such that $X + Y$ is uniformly distributed on its range. Are $X$ and $Y$ themselves uniformly distributed on their ranges?
- notes: Green, open problem 28
- track: open
- answer_shape: refute
- pair_id: G28
- pair_role: refute
- source_stem: 28
- source_namespace: Green28
- source_theorem: green_28
- source_category: research open
- source_ams: 60
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- True if a PMF on $\mathbb{Z}$ is uniformly distributed on its support. -/
def IsUniformOnSupport (X : PMF ℤ) : Prop :=
  ∃ (s : Finset ℤ) (hs : s.Nonempty), X = PMF.uniformOfFinset s hs

/--
The discrete convolution of two PMFs on $\mathbb{Z}$, representing the distribution of the sum of
two independent random variables.
-/
noncomputable def indepSum (X Y : PMF ℤ) : PMF ℤ := do
  let x ← X
  let y ← Y
  PMF.pure (x + y)

abbrev Target : Prop :=
    ¬ (
      ∀ (X Y : PMF ℤ), -- marginals, independence is built into indepSum
          X.support.Finite ∧ Y.support.Finite ∧ IsUniformOnSupport (indepSum X Y) →
            IsUniformOnSupport X ∧ IsUniformOnSupport Y
    )

end Problem
