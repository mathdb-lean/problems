import Mathlib
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

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

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: SingleLatticeCovering
- collection: openai-math
- question_id: openai-math:092
- source: openai-math
- source_locator: lean/ComparatorChallenges/SingleLatticeCovering.lean#OAI.SingleLatticeCovering.single_lattice_covering
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Determines the optimal worst-case covering density as $`\Theta(n\log n)`$, for both lattice and unrestricted translative coverings. Every convex body in ℝn, n ≥ 2, admits a lattice covering of density at most $`Cn\log n`$; centrally symmetric examples in every sufficiently large dimension require at least $`cn\log n`$ even without the lattice restriction, for absolute $`c,C\gt 0`$. ([Lean](lean/docs/092.md)) Every convex body in ℝn, n ≥ 2, admits a covering by translates along one full-rank lattice with density at most $`Cn\log n`$, for an absolute constant C. No symmetry or boundary regularity is assumed. For every sufficiently large dimension n, we construct a centrally symmetric convex body whose translative covering density exceeds $`c n\log n`$, where c &gt; 0 is absolute. This disproves the existence of a universal linear upper bound and matches the order of Rogers' upper bound.
- notes: OpenAI math result family 092, The optimal order of convex-body covering density -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/092.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SingleLatticeCovering.single_lattice_covering
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.LatticeCovering.Main
- source_main_result: OAI.SingleLatticeCovering.single_lattice_covering
- source_papers: preprints/A-single-lattice-covering-bound-of-order-n-log-n-September-23-2026/paper.pdf preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf
- source_scope_note: lean/docs/092.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Convex bodies and exact coverings by a single lattice in real coordinate space. -/

namespace SingleLatticeCovering

open MeasureTheory
open scoped Pointwise

abbrev Space (n : ℕ) := Fin n → ℝ

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def LatticeCovers {n : ℕ} (K : Set (Space n)) (L : Submodule ℤ (Space n)) : Prop :=
  K + (L : Set (Space n)) = Set.univ

def single_lattice_covering_statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n →
      ∀ (K : Set (Space n)), IsConvexBody K →
        ∃ (L : Submodule ℤ (Space n)) (_ : DiscreteTopology L),
          IsZLattice ℝ L ∧ LatticeCovers K L ∧
            (volume K).toReal / ZLattice.covolume L ≤ C * (n : ℝ) * Real.log (n : ℝ)

end SingleLatticeCovering

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SingleLatticeCovering.single_lattice_covering_statement

end Problem

/- Formalization scope, from lean/docs/092.md: The formalized result gives an absolute constant $C>0$ such that every convex body $K\subset\mathbb R^n$, $n\ge2$, admits a covering by translates along one full-rank lattice $L$ with density $|K|/\mathrm{covol}(L)\le Cn\log n$. The covering is exact, and no symmetry, boundary regularity, or volume normalization is assumed. The formalization determines the order of the largest covering density in dimension $n$. For all sufficiently large $n$, the suprema of translative covering density and lattice covering density are each bounded above and below by absolute positive multiples of $n\log n$, both over all convex bodies and over centrally symmetric convex bodies. -/
