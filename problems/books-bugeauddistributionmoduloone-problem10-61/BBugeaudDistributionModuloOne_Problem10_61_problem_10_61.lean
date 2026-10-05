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

- problem_id: BBugeaudDistributionModuloOne_Problem10_61_problem_10_61
- collection: books
- question_id: books:BugeaudDistributionModuloOne/Problem10_61
- source: formal-conjectures
- source_locator: FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_61.lean#problem_10_61
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Problem 10.61. Let $\alpha > 2$ be a Pisot number. For every $\xi \in C(\alpha)$ the sequence $(\xi \alpha^n)_{n \ge 1}$ is not uniformly distributed modulo one.
- notes: Book problem BugeaudDistributionModuloOne/Problem10_61 -- https://doi.org/10.13140/RG.2.2.13923.52001
- track: open
- answer_shape: proof
- source_stem: BugeaudDistributionModuloOne/Problem10_61
- source_namespace: Bugeaud61
- source_theorem: problem_10_61
- source_category: research open
- source_ams: 11 37
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: zero_mem_pisotCantorSet one_mem_pisotCantorSet
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The point of $C(\alpha)$ with digit sequence $\varepsilon$, that is
$(\alpha - 1) \sum_{k \ge 1} \varepsilon_k \alpha^{-k}$.
-/
noncomputable def cantorPoint (α : ℝ) (ε : ℕ → Bool) : ℝ :=
  (α - 1) * ∑' k : ℕ, (if ε k then (1 : ℝ) else 0) * α⁻¹ ^ (k + 1)

/--
The set $C(\alpha)$ of Problem 10.61. For $\alpha > 2$ it is a Cantor set of Hausdorff
dimension $\log 2 / \log \alpha < 1$, normalised so that $0$ is its least and $1$ its
greatest element.
-/
noncomputable def pisotCantorSet (α : ℝ) : Set ℝ := Set.range (cantorPoint α)

/--
The Route A exponent $A(\alpha) = \log 2 / \log \alpha + \log 2 / \log(1 / \rho)$ of
[Ste26], where $\rho$ is the largest modulus of a conjugate of $\alpha$ other than
$\alpha$ itself. It is the sum of the box dimensions of $C(\alpha)$ and of the window in
which the conjugate contributions live.
-/
noncomputable def routeAExponent (α ρ : ℝ) : ℝ :=
  Real.log 2 / Real.log α + Real.log 2 / Real.log ρ⁻¹

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
Sanity check: $0 \in C(\alpha)$, the point with all digits zero.
-/
@[category test, AMS 11 37]
theorem zero_mem_pisotCantorSet (α : ℝ) : 0 ∈ pisotCantorSet α :=
  ⟨fun _ => false, by simp [cantorPoint]⟩

/--
Sanity check: $1 \in C(\alpha)$ for $\alpha > 1$, the point with all digits one, since
$\sum_{k \ge 1} \alpha^{-k} = 1 / (\alpha - 1)$.
-/
@[category test, AMS 11 37]
theorem one_mem_pisotCantorSet {α : ℝ} (hα : 1 < α) : 1 ∈ pisotCantorSet α := by
  have hα0 : (0 : ℝ) < α := zero_lt_one.trans hα
  have hinv : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  refine ⟨fun _ => true, ?_⟩
  have hsum : ∑' k : ℕ, (if (fun _ : ℕ => true) k then (1 : ℝ) else 0) * α⁻¹ ^ (k + 1)
      = α⁻¹ * (1 - α⁻¹)⁻¹ := by
    simp only [if_true, one_mul, pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hinv]
  rw [cantorPoint, hsum]
  have h1 : α - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα)
  field_simp

abbrev Target : Prop :=
    ∀ (α : ℝ) (hα : IsPisot α) (hα2 : 2 < α),
      ∀ ξ ∈ pisotCantorSet α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

end Problem
