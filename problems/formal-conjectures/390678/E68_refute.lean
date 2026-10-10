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

- problem_id: E68_refute
- collection: erdos
- question_id: erdos:68
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/68.lean#erdos_68
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is $$\sum_{n=2}^\infty \frac{1}{n!-1}$$ irrational?
- notes: Erdos Problem 68 -- https://www.erdosproblems.com/68
- track: open
- answer_shape: refute
- pair_id: E68
- pair_role: refute
- source_stem: 68
- mathdb_ref: erdos:68
- source_namespace: Erdos68
- source_theorem: erdos_68
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: sum_factorial_inv_eq_geometric
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
$$\sum_{n=2}^\infty \frac{1}{n!-1} = \sum_{n=2}^\infty \sum_{k=1}^\infty \frac{1}{(n!)^k}$$
-/
@[category textbook, AMS 11]
theorem sum_factorial_inv_eq_geometric :
    let f (n k : ℕ) : ℝ := 1 / ((n + 2).factorial : ℝ) ^ (k + 1)
    ∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1) = ∑' n : ℕ, ∑' k : ℕ, f n k := by
  intro f
  apply tsum_congr
  intro n
  symm
  -- The inner sum is a geometric series with ratio r = ((n + 2)!)⁻¹.
  set r : ℝ := ((n + 2).factorial : ℝ)⁻¹ with hr_def
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_lt_one : r < 1 := inv_lt_one_of_one_lt₀ (by simp)
  -- Geometric series: HasSum (fun k ↦ r ^ k) ((1 - r)⁻¹)
  have hgeom := hasSum_geometric_of_lt_one hr_nonneg hr_lt_one
  -- Multiply by r to shift the index: HasSum (fun k ↦ r * r ^ k) (r * (1 - r)⁻¹)
  have hshift := hgeom.mul_left r
  -- Each summand satisfies f n k = r * r ^ k.
  have hf_eq : ∀ k, f n k = r * r ^ k := fun k => by simp only [f, hr_def]; ring
  -- Evaluate ∑' k, f n k = r * (1 - r)⁻¹ = 1 / ((n + 2)! - 1).
  exact ((hshift.congr_fun hf_eq).tsum_eq.trans (by simp only [hr_def]; field_simp))

abbrev Target : Prop :=
    ¬ (
      Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ))
    )

end Problem
