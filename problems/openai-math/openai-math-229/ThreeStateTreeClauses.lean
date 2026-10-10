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

- problem_id: ThreeStateTreeClauses
- collection: openai-math
- question_id: openai-math:229
- source: openai-math
- source_locator: lean/ComparatorChallenges/ThreeStateTreeClauses.lean#OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the exact reconstruction threshold $`d\lambda^2\gt 1`$, with nonreconstruction at equality, for three-state symmetric and four-state ferromagnetic broadcasting on regular trees (d ≥ 2) and observed Poisson trees (mean d &gt; 1 and d &gt; 0, respectively), with Poisson advantage averaged without conditioning on survival. The three-state theorem allows both signs of λ and gives the exact weak-recovery threshold for the symmetric three-community stochastic block model. ([Lean](lean/docs/229.md)) We determine the exact reconstruction threshold for the symmetric three-state broadcast process on every regular b-ary tree, b ≥ 2, and every observed Poisson Galton–Watson tree of mean d &gt; 1. Reconstruction occurs exactly when $`d\lambda^2\gt 1`$, with d = b in the regular model; there is non-reconstruction at equality for either sign of the channel parameter. The Poisson advantage is averaged over trees and spins without conditioning on survival. This resolves the all-degree three-state regular-tree prediction. Combining the Poisson theorem with known tree-to-graph and algorithmic results gives the exact weak-recovery threshold for the symmetric three-community sparse stochastic block model with independent uniform labels, fixed within- and between-community rates $`a,b\gt 0`$, and mean degree $`(a+2b)/3\gt 1`$: recovery is possible exactly when $`(a-b)^2\gt 3(a+2b)`$. Above this threshold it is achievable in $`O(n\log n)`$ time; at or below it, weak recovery is information-theoretically impossible.
- notes: OpenAI math result family 229, Exact three- and four-state reconstruction thresholds and four-state tree capacity -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/229.md
- track: solved
- answer_shape: proof
- context_lemmas: channelWeight_nonneg channelWeight_sum poissonWeight_nonneg poissonWeight_mass
- source_theorem: OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS OAI.ThreeState.TreeClauses.Tree.poisson_reconstructs_above_KS
- source_theorem_count: 2
- source_solution_module: OAI.Probability.ThreeStateClauses.Main
- source_papers: preprints/The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026/paper.pdf
- source_scope_note: lean/docs/229.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open Filter

namespace ThreeState.TreeClauses

abbrev Spin := Fin 3

def Admissible (lam : ℝ) : Prop := -(1 / 2 : ℝ) ≤ lam ∧ lam ≤ 1

def channelWeight (lam : ℝ) (i j : Spin) : ℝ :=
  if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3

lemma channelWeight_nonneg {lam : ℝ} (hlam : Admissible lam) (i j : Spin) :
    0 ≤ channelWeight lam i j := by
  unfold channelWeight
  split_ifs <;> dsimp [Admissible] at hlam <;> linarith [hlam.1, hlam.2]

lemma channelWeight_sum (lam : ℝ) (i : Spin) : ∑ j, channelWeight lam i j = 1 := by
  fin_cases i <;> simp [channelWeight, Fin.sum_univ_three] <;> ring

def channel (lam : ℝ) (hlam : Admissible lam) (i : Spin) : PMF Spin :=
  PMF.ofFintype (fun j ↦ ENNReal.ofReal (channelWeight lam i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ channelWeight_nonneg hlam i j),
      channelWeight_sum]
    norm_num)

def Observation : ℕ → Type
  | 0 => Spin
  | n + 1 => Multiset (Observation n)

def iidList {α : Type} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => p.bind fun x ↦ (iidList p n).map (List.cons x)

def observationLaw (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    (ℓ : ℕ) → Spin → PMF (Observation ℓ)
  | 0, i => PMF.pure i
  | ℓ + 1, i => offspring.bind fun n ↦
      (iidList ((channel lam hlam i).bind (observationLaw lam hlam offspring ℓ)) n).map
        (fun xs ↦ (xs : Multiset (Observation ℓ)))

def jointWeight (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (i : Spin) (o : Observation ℓ) : ℝ≥0∞ :=
  (1 / 3 : ℝ≥0∞) * observationLaw lam hlam offspring ℓ i o

def marginalWeight (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) : ℝ≥0∞ :=
  ∑ i, jointWeight lam hlam offspring ℓ i o

def posterior (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) (i : Spin) : ℝ :=
  (jointWeight lam hlam offspring ℓ i o / marginalWeight lam hlam offspring ℓ o).toReal

def advantage (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) : ℝ :=
  ∑' o : Observation ℓ, (marginalWeight lam hlam offspring ℓ o).toReal *
    ((∑ i : Spin, |posterior lam hlam offspring ℓ o i - (1 / 3 : ℝ)|) / 2)

def Reconstructs (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ Tendsto (advantage lam hlam offspring) atTop (nhds a)

namespace Probability

def poissonWeight (rate : ℝ) (count : ℕ) : ℝ :=
  Real.exp (-rate) * rate ^ count / (count.factorial : ℝ)

lemma poissonWeight_nonneg {rate : ℝ} (hrate : 0 ≤ rate) (count : ℕ) :
    0 ≤ poissonWeight rate count := by
  unfold poissonWeight
  positivity

lemma poissonWeight_mass (rate : ℝ≥0) : HasSum (poissonWeight rate) 1 :=
  ProbabilityTheory.hasSum_one_poissonMeasure rate

def _root_.OAI.ThreeState.TreeClauses.poissonPMF (rate : ℝ≥0) : PMF ℕ := by
  refine ⟨fun count ↦ ENNReal.ofReal (poissonWeight rate count), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← Real.toNNReal_one]
  exact (poissonWeight_mass rate).toNNReal (poissonWeight_nonneg rate.coe_nonneg)

end Probability

end ThreeState.TreeClauses

open scoped Topology
namespace ThreeState.TreeClauses.Tree

def regular_reconstructs_above_KS_statement : Prop :=
  ∀ (b : ℕ) (lam : ℝ) (hlam : Admissible lam) (hKS : 1 < (b:ℝ)*lam^2),
    Reconstructs lam hlam (PMF.pure b)

def poisson_reconstructs_above_KS_statement : Prop :=
  ∀ (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam) (hKS : 1 < (d:ℝ)*lam^2),
    Reconstructs lam hlam (poissonPMF d)

end ThreeState.TreeClauses.Tree

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS_statement ∧
  _root_.OAI.ThreeState.TreeClauses.Tree.poisson_reconstructs_above_KS_statement

end Problem

/- Formalization scope, from lean/docs/229.md: The formalization proves the supercritical direction of reconstruction for the symmetric three-state broadcast channel, whose parameter satisfies $-1/2\le\lambda\le1$. On a regular $b$-ary tree, reconstruction holds when $b\lambda^2>1$; on an observed Poisson Galton–Watson tree of mean $d$, it holds when $d\lambda^2>1$. In each case the root-estimation advantage converges to a positive limit, with the Poisson advantage averaged over trees and spins. The selected statements cover reconstruction above the Kesten–Stigum threshold. Non-reconstruction at or below the threshold and the stochastic-block-model consequences in the paper are outside them. -/
