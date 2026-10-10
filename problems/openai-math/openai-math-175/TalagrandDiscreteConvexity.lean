import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

- problem_id: TalagrandDiscreteConvexity
- collection: openai-math
- question_id: openai-math:175
- source: openai-math
- source_locator: lean/ComparatorChallenges/TalagrandDiscreteConvexity.lean#OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that integral and fractional expectation thresholds differ by at most a universal factor, and resolves Talagrand's discrete-convexity conjecture. An application proves the Ascoli–He–Park–Talagrand graph-decomposition conjecture: every graph's edges split into a universally bounded number of fixed pieces, each with containment threshold at most a universal constant times the original graph's integral expectation threshold. The pieces' embeddings need not agree on shared vertices. ([Lean](lean/docs/175.md)) We prove Talagrand's conjecture that integral and fractional expectation thresholds are within a universal constant factor, with the same covering budget. We prove Talagrand's discrete-convexity conjecture. There is a universal integer k such that, whenever an arbitrary family has Bernoulli product measure at least $`1-1/k`$, the sets not contained in a union of k members admit a cover of total cost at most 1/2 at the same density.
- notes: OpenAI math result family 175, Talagrand’s expectation thresholds, discrete convexity, and graph decompositions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/175.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.DiscreteConvexity.Main
- source_main_result: OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity
- source_papers: preprints/Integral-and-fractional-expectation-thresholds-are-equivalent-September-23-2026/paper.pdf preprints/Talagrands-discrete-convexity-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/175.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

abbrev Family (α : Type*) := Finset (Finset α)

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

/-- Independent Bernoulli coordinates, including every absent coordinate. -/
def bernoulliMass (p : ℝ) (s : Finset α) : ℝ :=
  p ^ s.card * (1 - p) ^ (Finset.univ \ s).card

/-- The probability of an arbitrary family, with no monotonicity condition. -/
def familyMeasure (p : ℝ) (D : Family α) : ℝ :=
  ∑ s ∈ D, bernoulliMass p s

/-- Each distinct generator is charged once at the original density. -/
def cost (p : ℝ) (G : Family α) : ℝ := ∑ I ∈ G, p ^ I.card

/-- Every covered set contains a generator. -/
def Covers (G A : Family α) : Prop := ∀ S ∈ A, ∃ I ∈ G, I ⊆ S

/-- An actual finite containment cover with total cost at most one half. -/
def Small (p : ℝ) (A : Family α) : Prop :=
  ∃ G : Family α, Covers G A ∧ cost p G ≤ 1 / 2

/-- Exactly `k` entries, with no distinctness or disjointness restriction. -/
def unionTuple {k : ℕ} (f : Fin k → Finset α) : Finset α :=
  Finset.univ.biUnion f

/-- All subsets contained in no union of `k` members of the given family. -/
def exceptional (k : ℕ) (D : Family α) : Family α := by
  classical
  exact Finset.univ.filter (fun S =>
    ∀ f : Fin k → Finset α, (∀ j, f j ∈ D) → ¬ S ⊆ unionTuple f)

/-- Smallness at the original density for every positive ground-set size. -/
def talagrand_discrete_convexity_statement : Prop :=
  ∀ (N : ℕ) (_hN : 1 ≤ N) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (D : Family (Fin N)) (hD : 1 - 1 / (2 : ℝ) ^ 75 ≤ familyMeasure p D),
    Small p (exceptional ((2 : ℕ) ^ 75) D)

end

end TalagrandDiscreteConvexity

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity_statement

end Problem

/- Formalization scope, from lean/docs/175.md: Talagrand's expectation-threshold conjecture asks whether the fractional and integral expectation thresholds are comparable by an absolute constant. The formalized result proves $q_f(\mathcal F)\le25\cdot512^4 q(\mathcal F)$ for every nonempty proper increasing family on a finite nonempty ground set. Both thresholds use cover budget $1/2$, and fractional covers may assign weights to every subset, including the empty set. The formalized result proves Talagrand's discrete-convexity assertion with $k=2^{75}$. If a family of subsets of a finite nonempty ground set has Bernoulli-$p$ measure at least $1-1/k$, then the sets not contained in a union of $k$ members form a $p$-small family: they have a containment cover of total $p$-cost at most $1/2$. This holds for every $0<p<1$, with repeated members allowed in the union and no monotonicity assumption. -/
