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

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Logic.Equiv.Defs

/-!
Bergström’s conjecture on the Euclidean Steinitz constant (MathDB 368422).
Authored directly from the mathematical source.

- problem_id: AEuclideanSteinitz
- collection: authored
- question_id: authored:EuclideanSteinitz
- source: mathdb-lean
- source_locator: problems/368422/AEuclideanSteinitz.lean#Problem.Target
- prose: There is an absolute positive constant C such that in every dimension d >= 1 every finite zero-sum family of vectors in the Euclidean unit ball can be reordered so that all partial sums have norm at most C times sqrt(d).
- notes: https://mathdb.com/p/368422/bergstrom-s-conjecture-on-the-euclidean-steinitz-constant
- track: open
- answer_shape: proof

Reference: Ambrus and Heck, A note on the Steinitz Lemma, arXiv:2505.09465v3, Conjecture 5 and the definitions preceding it. https://arxiv.org/html/2505.09465v3

The absolute constant is chosen before the dimension and the vector family. Finite indexed families permit repeated vectors, as in the primary source. A permutation reorders the entire family, and every partial sum is checked. MathDB says this was refuted, but the cited source says it has refuted all attempts, meaning attempts to solve it. The source still presents Conjecture 5 as open; this contribution follows that source rather than the erroneous status sentence.
-/

namespace Problem

/-- Bergström’s uniform square-root bound, expressed without an infimum over constants. -/
abbrev Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d →
    ∀ N : ℕ, ∀ v : Fin N → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖v i‖ ≤ 1) → (∑ i, v i) = 0 →
        ∃ σ : Equiv.Perm (Fin N), ∀ k : ℕ, k ≤ N →
          ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), v (σ i)‖ ≤
            C * Real.sqrt (d : ℝ)

end Problem
