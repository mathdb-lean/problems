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

- problem_id: G22
- collection: green
- question_id: green:22
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/22.lean#green_22
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $\{1, \ldots, N\}$ is $r$-coloured then, for $N \geqslant N_0(r)$, there are integers $x, y \geqslant 3$ such that $x + y, xy$ have the same colour. Find reasonable bounds for $N_0(r)$. The goal is to improve upon the Green-Sawhney bound.
- notes: Green, open problem 22
- track: open
- answer_shape: value
- answer_type: ℕ → ℝ
- answer_pinned: false
- answer_pinned_reason: infinitely_many_trivial_witnesses
- source_stem: 22
- source_namespace: Green22
- source_theorem: green_22
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset Filter

namespace Problem

/--
The monochromatic sum-product property: a colouring $c$ of $\{1, \ldots, N\}$ has a pair $(x, y)$
with $x, y \geq 3$ such that $x + y$ and $xy$ are both in $\{1, \ldots, N\}$ and receive the same
colour.
-/
def HasMonochromaticSumProduct (N : ℕ) (r : ℕ) (coloring : Icc 1 N → Fin r) : Prop :=
  ∃ x y : ℕ, 3 ≤ x ∧ 3 ≤ y ∧
    ∃ h_sum : x + y ∈ Icc 1 N, ∃ h_prod : x * y ∈ Icc 1 N,
      coloring ⟨x + y, h_sum⟩ = coloring ⟨x * y, h_prod⟩

/--
$N_0(r)$ is the smallest $N$ such that every $r$-colouring of $\{1, \ldots, N\}$ has the
monochromatic sum-product property.
-/
noncomputable def N₀ (r : ℕ) : ℕ :=
  sInf {N | ∀ c : Icc 1 N → Fin r, HasMonochromaticSumProduct N r c}

open scoped Asymptotics

/-- The upper bound function from [GrSa25]. -/
noncomputable def GreenSawhneyBound (r : ℕ) : ℝ := Real.exp (Real.exp (r ^ 50))

abbrev Target (value : ℕ → ℝ) : Prop :=
    let ans := value
    ∀ᶠ r in atTop, N₀ r ≤ ans r ∧
    ans =o[atTop] GreenSawhneyBound

end Problem
