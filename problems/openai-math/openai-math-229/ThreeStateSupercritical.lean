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

- problem_id: ThreeStateSupercritical
- collection: openai-math
- question_id: openai-math:229
- source: openai-math
- source_locator: lean/ComparatorChallenges/ThreeStateSupercritical.lean#OAI.ThreeState.regular_supercritical
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the exact reconstruction threshold $`d\lambda^2\gt 1`$, with nonreconstruction at equality, for three-state symmetric and four-state ferromagnetic broadcasting on regular trees (d ≥ 2) and observed Poisson trees (mean d &gt; 1 and d &gt; 0, respectively), with Poisson advantage averaged without conditioning on survival. The three-state theorem allows both signs of λ and gives the exact weak-recovery threshold for the symmetric three-community stochastic block model. ([Lean](lean/docs/229.md)) We determine the exact reconstruction threshold for the symmetric three-state broadcast process on every regular b-ary tree, b ≥ 2, and every observed Poisson Galton–Watson tree of mean d &gt; 1. Reconstruction occurs exactly when $`d\lambda^2\gt 1`$, with d = b in the regular model; there is non-reconstruction at equality for either sign of the channel parameter. The Poisson advantage is averaged over trees and spins without conditioning on survival. This resolves the all-degree three-state regular-tree prediction. Combining the Poisson theorem with known tree-to-graph and algorithmic results gives the exact weak-recovery threshold for the symmetric three-community sparse stochastic block model with independent uniform labels, fixed within- and between-community rates $`a,b\gt 0`$, and mean degree $`(a+2b)/3\gt 1`$: recovery is possible exactly when $`(a-b)^2\gt 3(a+2b)`$. Above this threshold it is achievable in $`O(n\log n)`$ time; at or below it, weak recovery is information-theoretically impossible.
- notes: OpenAI math result family 229, Exact three- and four-state reconstruction thresholds and four-state tree capacity -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/229.md
- track: solved
- answer_shape: proof
- context_lemmas: channel_nonneg channel_sum
- source_theorem: OAI.ThreeState.regular_supercritical OAI.ThreeState.poisson_supercritical
- source_theorem_count: 2
- source_solution_module: OAI.Probability.ThreeState.Main
- source_papers: preprints/The-exact-reconstruction-threshold-for-the-three-state-symmetric-channel-September-25-2026/paper.pdf
- source_scope_note: lean/docs/229.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace ThreeState

abbrev Spin := Fin 3

 
def Admissible (lam : ℝ) : Prop := -(1 / 2 : ℝ) ≤ lam ∧ lam ≤ 1

 
noncomputable def channel (lam : ℝ) (i j : Spin) : ℝ :=
  if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3

 

def Observation : ℕ → Type
  | 0 => Spin
  | n + 1 => Multiset (Observation n)

theorem channel_nonneg {lam : ℝ} (h : Admissible lam) (i j : Spin) :
    0 ≤ channel lam i j := by
  unfold channel
  split_ifs
  · dsimp [Admissible] at h
    linarith [h.1]
  · dsimp [Admissible] at h
    linarith [h.2]

theorem channel_sum (lam : ℝ) (i : Spin) : ∑ j, channel lam i j = 1 := by
  fin_cases i <;> simp [channel, Fin.sum_univ_succ] <;> ring

noncomputable def channelPMF (lam : ℝ) (h : Admissible lam) (i : Spin) : PMF Spin :=
  PMF.ofFintype (fun j => ENNReal.ofReal (channel lam i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => channel_nonneg h i j)]
    simp [channel_sum])

 
noncomputable def iidList {α : Type*} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => p.bind fun a => (iidList p n).map (List.cons a)

 

noncomputable def observedLaw (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    (n : ℕ) → Spin → PMF (Observation n)
  | 0, i => PMF.pure i
  | n + 1, i => offspring.bind fun k =>
      (iidList ((channelPMF lam h i).bind (observedLaw offspring lam h n)) k).map
        (fun xs : List (Observation n) => (xs : Multiset (Observation n)))

noncomputable def uniformSpin : PMF Spin := PMF.ofFintype (fun _ => 1 / 3) (by
  simp
  exact ENNReal.mul_inv_cancel (by norm_num) (by finiteness))

 
noncomputable def marginal {α : Type*} (law : Spin → PMF α) : PMF α :=
  uniformSpin.bind law

 
noncomputable def posterior {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) : ℝ :=
  if marginal law y = 0 then 1 / 3
  else (law i y).toReal / (3 * (marginal law y).toReal)

 

noncomputable def advantage {α : Type*} (law : Spin → PMF α) : ℝ :=
  ∑' y, (marginal law y).toReal *
    ((∑ i : Spin, |posterior law y i - 1 / 3|) / 2)

noncomputable def regularLaw (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) :=
  observedLaw (PMF.pure b) lam h n

 
noncomputable def poissonOffspring (d : ℝ) (hd : 0 ≤ d) : PMF ℕ := by
  refine ⟨fun k => ENNReal.ofReal (Real.exp (-d) * d ^ k / (k.factorial : ℝ)), ?_⟩
  apply ENNReal.hasSum_coe.2
  have hsum : HasSum (fun k : ℕ => Real.exp (-d) * d ^ k / (k.factorial : ℝ)) 1 :=
    ProbabilityTheory.hasSum_one_poissonMeasure ⟨d, hd⟩
  simpa using hsum.toNNReal (fun k => by positivity)

noncomputable def poissonLaw (d : ℝ) (hd : 0 ≤ d) (lam : ℝ)
    (h : Admissible lam) (n : ℕ) :=
  observedLaw (poissonOffspring d hd) lam h n

noncomputable def regularAdvantage (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) : ℝ :=
  advantage (regularLaw b lam h n)

noncomputable def poissonAdvantage (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam) (n : ℕ) : ℝ :=
  advantage (poissonLaw d (le_trans (by norm_num) hd.le) lam h n)

 
def Reconstructs (a : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ Filter.Tendsto a Filter.atTop (nhds L)

def regular_supercritical_statement : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam) (hcrit : 1 < (b : ℝ) * lam ^ 2),
    Reconstructs (regularAdvantage b lam h)

def poisson_supercritical_statement : Prop :=
  ∀ (d : ℝ) (hd : 1 < d) (lam : ℝ) (h : Admissible lam) (hcrit : 1 < d * lam ^ 2),
    Reconstructs (poissonAdvantage d hd lam h)

end ThreeState

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ThreeState.regular_supercritical_statement ∧
  _root_.OAI.ThreeState.poisson_supercritical_statement

end Problem

/- Formalization scope, from lean/docs/229.md: The formalization proves the supercritical direction of reconstruction for the symmetric three-state broadcast channel, whose parameter satisfies $-1/2\le\lambda\le1$. On a regular $b$-ary tree, reconstruction holds when $b\lambda^2>1$; on an observed Poisson Galton–Watson tree of mean $d$, it holds when $d\lambda^2>1$. In each case the root-estimation advantage converges to a positive limit, with the Poisson advantage averaged over trees and spins. The selected statements cover reconstruction above the Kesten–Stigum threshold. Non-reconstruction at or below the threshold and the stochastic-block-model consequences in the paper are outside them. -/
