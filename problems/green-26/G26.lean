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

- problem_id: G26
- collection: green
- question_id: green:26
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/26.lean#green_26
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A_1, \dots, A_{100}$ be "cubes" in $\mathbb{F}^n_3$. Is it true that $A_1 + \dots + A_{100} = \mathbb{F}^n_3$?
- notes: Green, open problem 26 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.26
- track: solved
- answer_shape: proof
- source_stem: 26
- source_namespace: Green26
- source_theorem: green_26
- source_category: research solved
- source_ams: 5 11 15
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set
open scoped Pointwise

namespace Problem

/-- The standard cube in $\mathbb{F}_p^n$ is the set of points with coordinates in $\{0, 1\}$. -/
def StandardCube {p : ℕ} [Fact p.Prime] (n : ℕ) : Set (𝔽 p n) :=
  {x | ∀ i, x i = 0 ∨ x i = 1}

/-- A cube is the image of $\lbrace 0, 1\rbrace^n$ under a linear automorphism. -/
def IsCube {p n : ℕ} [Fact p.Prime] (A : Set (𝔽 p n)) : Prop :=
  ∃ φ : 𝔽 p n ≃ₗ[ZMod p] 𝔽 p n, A = φ '' StandardCube n

open Asymptotics Filter

abbrev Target : Prop :=
    ∀ n : ℕ,
      ∀ A : Fin 100 → Set (𝔽₃ n), (∀ i, IsCube (A i)) →
      ∑ i, A i = univ

end Problem
