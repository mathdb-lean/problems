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

- problem_id: G18_prove
- collection: green
- question_id: green:18
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/18.lean#green_18
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that $G$ is a finite group, and let $A \subset G \times G$ be a subset of density $\alpha$. Is it true that there are $\gg_\alpha |G|^3$ triples $x, y, g$ such that $(x, y), (gx, y), (x, gy)$ all lie in $A$? Note: A is taken as $\alpha$-dense, i.e. $|A| \ge \alpha |G|^2$ [Au16, Question 2]
- notes: Green, open problem 18 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.18
- track: open
- answer_shape: prove
- pair_id: G18
- pair_role: prove
- source_stem: 18
- source_namespace: Green18
- source_theorem: green_18
- source_category: research open
- source_ams: 5 11 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset

namespace Problem

/--
The number of triples $(x, y, g)$ in $G^3$ such that $g \neq e$, and $(x, y), (gx, y), (x, gy)$ are
all in $A$. These are called "naive corners" by [Au16].

Note: the shortened formulation from [Gr26] does not mention $g \neq e$, but this is the original
statement from [Au16], which ensure non-trivial corners. Note however that [Au16] use more
generally compact groups and not just finite discrete groups.
-/
def numNaiveCorners {G : Type*} [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)) : ℕ :=
  ( (univ : Finset (G × G × G)).filter
    fun ⟨x, y, g⟩ => g ≠ 1 ∧ (x, y) ∈ A ∧ (g * x, y) ∈ A ∧ (x, g * y) ∈ A
  ).card

/--
The number of triples $(x, y, g)$ in $G^3$ such that $g \neq e$, and $(x, y), (xg, y), (x, gy)$ are
all in $A$. These are called "BMZ corners" by [Au16].
-/
def numBmzCorners {G : Type*} [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)) : ℕ :=
  (
    (univ : Finset (G × G × G)).filter
    fun ⟨x, y, g⟩ => g ≠ 1 ∧ (x, y) ∈ A ∧ (x * g, y) ∈ A ∧ (x, g * y) ∈ A
  ).card

abbrev Target : Prop :=
    ∀ α > 0, ∃ c > 0, ∃ m₀ : ℕ,
          ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)),
          Fintype.card G ≥ m₀ →
          (A.card : ℝ) ≥ α * (Fintype.card G) ^ 2 →
          (numNaiveCorners A : ℝ) ≥ c * (Fintype.card G) ^ 3

end Problem
