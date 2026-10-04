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

- problem_id: E254
- collection: erdos
- question_id: erdos:254
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/254.lean#erdos_254
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{N}$ be such that $\lvert A\cap [1,2x]\rvert -\lvert A\cap [1,x]\rvert \to \infty\textrm{ as }x\to \infty$ and $\sum_{n\in A} \{ \theta n\}=\infty$ for every $\theta\in (0,1)$, where $\{x\}$ is the distance of $x$ from the nearest integer. Then every sufficiently large integer is the sum of distinct elements of $A$.
- notes: Erdos Problem 254 -- https://www.erdosproblems.com/254
- track: solved
- answer_shape: proof
- source_stem: 254
- mathdb_ref: erdos:254
- source_namespace: Erdos254
- source_theorem: erdos_254
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: not_summable_iff_tendsto_partial_sums
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Set

namespace Problem

/--
An integer `n` can be written as a sum of distinct elements of `A`.
-/
def IsSumOfDistinct (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ S.sum (fun x ↦ x) = n

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The hypothesis `¬ Summable (fun n : A ↦ distToNearestInt (θ * n))` used below says exactly
that the partial sums of `‖θ n‖` over `n ∈ A` diverge, which is the form the linked proof uses.
`distToNearestInt` is nonnegative, so this is an instance of
`not_summable_subtype_iff_tendsto_sum_indicator`. -/
@[category API, AMS 11]
theorem not_summable_iff_tendsto_partial_sums (A : Set ℕ) (θ : ℝ) :
    ¬ Summable (fun n : A ↦ distToNearestInt (θ * (n : ℝ))) ↔
      Tendsto (fun N : ℕ =>
          ∑ n ∈ Finset.range N, A.indicator (fun n => distToNearestInt (θ * (n : ℝ))) n)
        atTop atTop :=
  not_summable_subtype_iff_tendsto_sum_indicator
    (f := fun m : ℕ => distToNearestInt (θ * (m : ℝ))) fun _ => distToNearestInt_nonneg _

abbrev Target : Prop :=
    ∀ (A : Set ℕ),
      (Tendsto (fun x : ℕ ↦ (A ∩ Icc 1 (2 * x)).ncard - (A ∩ Icc 1 x).ncard) atTop atTop) ∧
      (∀ θ : ℝ, 0 < θ → θ < 1 → ¬ Summable (fun n : A ↦ distToNearestInt (θ * (n : ℝ)))) →
        ∀ᶠ m in atTop, IsSumOfDistinct A m

end Problem
