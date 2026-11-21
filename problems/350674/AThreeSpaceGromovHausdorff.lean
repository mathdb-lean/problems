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

import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
Three-space common ambient realization conjecture for Gromov-Hausdorff distance (MathDB 350674).
Authored directly from the mathematical source.

- problem_id: AThreeSpaceGromovHausdorff
- collection: authored
- question_id: authored:ThreeSpaceGromovHausdorff
- source: mathdb-lean
- source_locator: problems/350674/AThreeSpaceGromovHausdorff.lean#Problem.Target
- prose: Any three nonempty compact metric spaces have isometric embeddings into one compact metric space such that all pairwise Hausdorff distances of the images equal the corresponding Gromov-Hausdorff distances.
- notes: https://mathdb.com/p/350674/three-space-common-ambient-realization-conjecture-for-gromov
- track: open
- answer_shape: proof

Reference: Memoli and Wan, Characterization of Gromov-type geodesics, arXiv:2105.05369v2, Section 6, Conjecture 2. https://arxiv.org/html/2105.05369v2

The same ambient space and the same three embeddings must realize all pairs simultaneously. Nonempty is explicit, as in the Hausdorff-distance convention of Definition 2.7 and in Mathlib ghDist. Isometry implies injectivity for metric spaces. The target is a closed proposition: all spaces and instances are quantified inside it. Using Type introduces no restriction on compact metric spaces up to isometry, since such spaces admit small representatives.
-/

namespace Problem

/-- Simultaneous optimal realization for three nonempty compact metric spaces. -/
abbrev Target : Prop :=
  ∀ (X : Fin 3 → Type) [∀ i, MetricSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)],
    ∃ (Z : Type) (_ : MetricSpace Z), CompactSpace Z ∧
      ∃ φ : ∀ i, X i → Z, (∀ i, Isometry (φ i)) ∧
        ∀ i j, Metric.hausdorffDist (Set.range (φ i)) (Set.range (φ j)) =
          GromovHausdorff.ghDist (X i) (X j)

end Problem
