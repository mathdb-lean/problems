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

- problem_id: HalvingLines
- collection: openai-math
- question_id: openai-math:183
- source: openai-math
- source_locator: lean/ComparatorChallenges/HalvingLines.lean#OAI.PlanarHalving.power_bounds
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Improves the planar halving-line bound to $`O(n^{4/3-\varepsilon})`$ for sets with no three collinear and an absolute ε &gt; 0. More generally, an n-point set with no three collinear has $`O(n(k+1)^{1/3-\varepsilon_0})`$ strictly separable k-subsets for $`1\le k\le n/2`$, with an absolute $`\varepsilon_0\gt 0`$. The constants and positive exponents are nonquantitative. ([Lean](lean/docs/183.md)) There are absolute constants ε &gt; 0 and C such that every sufficiently large even n-point set in the plane with no three collinear has at most $`Cn^{4/3-\varepsilon}`$ unordered halving pairs. This gives a power saving over the classical $`O(n^{4/3})`$ bound for planar halving lines. The proof is nonquantitative and does not supply explicit constants.
- notes: OpenAI math result family 183, Power savings for planar halving lines and <i>k</i>-sets -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/183.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PlanarHalving.power_bounds
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.HalvingLines.Main
- source_papers: preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf
- source_scope_note: lean/docs/183.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace PlanarHalving

abbrev Point := ℝ × ℝ

def orient (p q r : Point) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

def GeneralPosition {n : ℕ} (P : Fin n → Point) : Prop :=
  Function.Injective P ∧ ∀ i j l, i ≠ j → j ≠ l → i ≠ l →
    orient (P i) (P j) (P l) ≠ 0

noncomputable def sideCount {n : ℕ} (P : Fin n → Point) (i j : Fin n) : ℕ :=
  (Finset.univ.filter fun l => 0 < orient (P i) (P j) (P l)).card

noncomputable def halvingCount {n : ℕ} (P : Fin n → Point) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ sideCount P ij.1 ij.2 = (n - 2) / 2 ∧
      sideCount P ij.2 ij.1 = (n - 2) / 2).card

noncomputable def slope (p q : Point) : ℝ := (q.2 - p.2) / (q.1 - p.1)

def Generic {n : ℕ} (P : Fin n → Point) : Prop :=
  GeneralPosition P ∧
  (∀ i j, i ≠ j → (P i).1 ≠ (P j).1) ∧
  (∀ i j a b, i < j → a < b → slope (P i) (P j) = slope (P a) (P b) →
    i = a ∧ j = b) ∧
  (∀ i j a b c d, i < j → a < b → c < d →
    (i, j) ≠ (a, b) → (c, d) ≠ (i, j) → (c, d) ≠ (a, b) →
    ∀ z : Point, z ∈ openSegment ℝ (P i) (P j) →
      z ∈ openSegment ℝ (P a) (P b) → z ∉ segment ℝ (P c) (P d))

noncomputable def belowCount {n : ℕ} (P : Fin n → Point) (i j : Fin n) : ℕ :=
  let s := slope (P i) (P j)
  (Finset.univ.filter fun l => (P l).2 - s * (P l).1 <
    (P i).2 - s * (P i).1).card

noncomputable def switchCount {n : ℕ} (P : Fin n → Point) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ 0 < k ∧ k < n ∧ belowCount P ij.1 ij.2 = k - 1).card

def power_bounds_statement : Prop :=
  (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∃ n₀ : ℕ,
      ∀ n : ℕ, Even n → n₀ ≤ n → ∀ P : Fin n → Point,
        GeneralPosition P → (halvingCount P : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε)) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ P : Fin n → Point, Generic P →
        ∀ k : ℕ, k ≤ n → (switchCount P k : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε))

end PlanarHalving

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PlanarHalving.power_bounds_statement

end Problem

/- Formalization scope, from lean/docs/183.md: A halving pair in an even planar point set is a pair whose line leaves equally many remaining points on each side. The formalization proves that some absolute $\varepsilon>0$ and $C$ bound the number of halving pairs by $Cn^{4/3-\varepsilon}$ for every sufficiently large even $n$ and every $n$-point set with no three collinear. It also proves a bound of the same form for all level-switch counts under the additional generic-position assumptions in the statement. The constants are existential. -/
