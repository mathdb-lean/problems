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

- problem_id: PlanarUnitDistances
- collection: openai-math
- question_id: openai-math:167
- source: openai-math
- source_locator: lean/ComparatorChallenges/PlanarUnitDistances.lean#OAI.PlanarUnitDistances.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the weak pinned Erdős distance conjecture: for every fixed ε &gt; 0, all but $`o(n)`$ points of any n-point planar set determine at least $`n^{1-\varepsilon}`$ distinct nonzero distances. A complementary theorem bounds the number of unit-distance pairs by $`O(n^{4/3-\delta})`$ for an absolute δ &gt; 0. ([Lean](lean/docs/167.md)) We prove the weak pinned Erdős distinct-distance conjecture. For every fixed ε &gt; 0, all but $`o(n)`$ points of any n-point planar set determine at least $`n^{1-\varepsilon}`$ distinct nonzero distances. We prove a power saving for the planar unit-distance problem: for some absolute $`\beta\lt 4/3`$, every set of n points in the Euclidean plane determines $`O(n^\beta)`$ unordered pairs at unit distance.
- notes: OpenAI math result family 167, Planar distinct distances and unit-distance bounds -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/167.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PlanarUnitDistances.main
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.UnitDistances.Main
- source_papers: preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/paper.pdf preprints/A-power-saving-for-planar-unit-distances-September-23-2026/paper.pdf
- source_scope_note: lean/docs/167.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace PlanarUnitDistances

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsUnitPair : Sym2 Plane → Prop :=
  Sym2.lift ⟨fun x y => dist x y = 1, fun x y => by dsimp; rw [dist_comm]⟩

noncomputable def unitPairCount (X : Finset Plane) : ℕ := by
  classical
  exact (X.sym2.filter IsUnitPair).card

noncomputable def u (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ X : Finset Plane, X.card = n ∧ unitPairCount X = m}

def main_statement : Prop :=
  ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < (4 : ℝ) / 3 ∧
    ∀ n : ℕ, (u n : ℝ) ≤ C * (n : ℝ) ^ β

end PlanarUnitDistances

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PlanarUnitDistances.main_statement

end Problem

/- Formalization scope, from lean/docs/167.md: The formalized result shows that large repeated distance fibers are rare in arbitrary finite planar point sets. For each fixed $s>0$, the largest possible fraction of ordered distinct pairs $(x,y)$ whose distance from the pin $x$ occurs at least $n^s$ times tends to zero as the set size $n$ grows. Consequently, for every $\varepsilon>0$, the fraction of pins determining fewer than $n^{1-\varepsilon}$ distances tends uniformly to zero. The separate unit-distance power-saving theorem is not included. The planar unit-distance problem asks how many pairs at distance one can occur among $n$ points. The formalization proves that there are absolute constants $C>0$ and $1\le\beta<4/3$ such that every finite planar point set of size $n$ determines at most $Cn^\beta$ unordered unit-distance pairs. The same constants work for every $n$, giving a fixed power improvement over the classical exponent $4/3$. -/
