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

- problem_id: E755
- collection: erdos
- question_id: erdos:755
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/755.lean#erdos_755
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Erdős asked whether every $n$-point set in $\mathbb{R}^6$ spans at most $(1/27 + o(1)) n^3$ unit equilateral triangles. Clemen, Dumitrescu, and Liu [CDL25b] proved the stronger any-size statement $T_6(n) = (1/27 + o(1)) n^3$. The unit-triangle upper bound follows as a corollary, since unit equilateral triangles are a subset of equilateral triangles of any positive side length: $T_\mathrm{unit} \leq T_\mathrm{anysize}$.
- notes: Erdos Problem 755 -- https://www.erdosproblems.com/755
- track: solved
- answer_shape: decide
- source_stem: 755
- mathdb_ref: erdos:755
- source_namespace: Erdos755
- source_theorem: erdos_755
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Metric
open scoped EuclideanGeometry Asymptotics

namespace Problem

/-- A three-point set whose pairwise distances are all equal to `side`. -/
def IsEquilateralTriangle {d : ℕ} (side : ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  T.card = 3 ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = side

/-- A unit equilateral triangle in Euclidean `d`-space. -/
def IsUnitEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsEquilateralTriangle 1 T

/-- An equilateral triangle of any positive side length in Euclidean `d`-space. -/
def IsAnySizeEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ side : ℝ, 0 < side ∧ IsEquilateralTriangle side T

/-- Number of unit equilateral triangles spanned by a finite point set. -/
noncomputable def unitEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsUnitEquilateralTriangle T).card

/-- Number of equilateral triangles of any positive side length spanned by a finite point set. -/
noncomputable def anySizeEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsAnySizeEquilateralTriangle T).card

/-- Maximum number of unit equilateral triangles spanned by $n$ points in $\mathbb{R}^d$. -/
noncomputable def TUnit (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ unitEquilateralTriangleCount d P = m}

/-- Maximum number of equilateral triangles of any size spanned by $n$ points in $\mathbb{R}^d$. -/
noncomputable def TAnySize (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ anySizeEquilateralTriangleCount d P = m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ o : ℕ → ℝ,
      o =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
        ∀ᶠ n in atTop,
          (TUnit 6 n : ℝ) ≤ ((1 / 27 : ℝ) + o n) * (n : ℝ) ^ 3

end Problem
