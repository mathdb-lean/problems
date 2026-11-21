/-
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

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.HausdorffDimension
import FormalConjecturesForMathlib.NumberTheory.MultiplicativelyIndependent

/-!
Furstenberg's dimension conjecture for multiplicatively independent orbits (MathDB 349088).
Authored directly from the mathematical source.

- problem_id: AFurstenbergOrbitDimensions
- collection: authored
- question_id: authored:FurstenbergOrbitDimensions
- source: mathdb-lean
- source_locator: problems/349088/AFurstenbergOrbitDimensions.lean#Problem.Target
- prose: For multiplicatively independent integer bases p and q at least two, the Hausdorff dimensions of the closures of the two forward multiplication orbits of an irrational point of the circle sum to at least one.
- notes: https://mathdb.com/p/349088/furstenberg-s-dimension-conjecture-for-multiplicatively-inde
- track: open
- answer_shape: proof

Reference: Adamczewski and Faverjon, Mahler's method in several variables and finite automata, arXiv:2012.08283v1, Appendix A, Conjecture A.1. https://arxiv.org/pdf/2012.08283

UnitAddCircle is R/Z with its quotient metric. The orbit includes the initial point (iterate zero). Taking closure is essential: the orbit itself is countable. Irrationality is imposed on the representative x in [0,1). The pinned dependency defines multiplicative independence by irrationality of log(p)/log(q). Hausdorff dimension on the circle agrees with the interval-representative convention via finitely many local isometries; the possible endpoint difference has dimension zero.
-/

open MeasureTheory

namespace Problem

/-- Closure in the circle of the forward multiplication orbit, including iterate zero. -/
def orbitClosure (q : ℕ) (x : ℝ) : Set UnitAddCircle :=
  closure (Set.range (fun k : ℕ => (q ^ k) • (x : UnitAddCircle)))

/-- Conjecture A.1; the two bases must be multiplicatively independent. -/
abbrev Target : Prop :=
  ∀ p q : ℕ, 2 ≤ p → 2 ≤ q → Nat.MultiplicativelyIndependent p q →
    ∀ x ∈ Set.Ico (0 : ℝ) 1, Irrational x →
      1 ≤ dimH (orbitClosure p x) + dimH (orbitClosure q x)

end Problem
