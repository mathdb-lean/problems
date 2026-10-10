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

- problem_id: CriticalZ3
- collection: openai-math
- question_id: openai-math:213
- source: openai-math
- source_locator: lean/ComparatorChallenges/CriticalZ3.lean#OAI.CriticalZ3.critical_no_infinite
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the Benjamini–Schramm criticality conjecture for bond percolation on every infinite connected locally finite quasi-transitive graph with $`p_c\lt 1`$: at the critical probability, there is almost surely no infinite cluster. The family also establishes this conclusion for both nearest-neighbor bond and site percolation on ℤ3. ([Lean](lean/docs/213.md)) We prove that nearest-neighbor Bernoulli bond and site percolation on ℤ3 have no infinite cluster at their respective critical parameters. The proof combines a finite connection inequality for independent hyperedges with a finite-scale extension estimate and an adaptive exploration. We prove that critical Bernoulli bond percolation has no infinite cluster on any infinite connected locally finite quasi-transitive graph with critical probability less than one. This resolves the bond form of the criticality conjecture of Benjamini and Schramm.
- notes: OpenAI math result family 213, Critical percolation on every quasi-transitive graph -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/213.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CriticalZ3.critical_no_infinite
- source_theorem_count: 1
- source_solution_module: OAI.Probability.CriticalZ3.Main
- source_main_result: OAI.CriticalZ3.critical_no_infinite
- source_papers: preprints/Critical-bond-and-site-percolation-on-the-cubic-lattice-September-24-2026/paper.pdf preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf
- source_scope_note: lean/docs/213.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory

namespace CriticalZ3

abbrev Vertex := Fin 3 → ℤ
abbrev Bond := Vertex × Fin 3
abbrev BondConfig := Bond → Bool
abbrev SiteConfig := Vertex → Bool

def step (x : Vertex) (i : Fin 3) : Vertex := fun j => x j + if i = j then 1 else 0

def NearestNeighbor (x y : Vertex) : Prop :=
  ∃ i : Fin 3, y = step x i ∨ x = step y i

def BondOpen (ω : BondConfig) (x y : Vertex) : Prop :=
  (∃ i : Fin 3, y = step x i ∧ ω (x, i) = true) ∨
  (∃ i : Fin 3, x = step y i ∧ ω (y, i) = true)

def SiteOpen (ω : SiteConfig) (x y : Vertex) : Prop :=
  NearestNeighbor x y ∧ ω x = true ∧ ω y = true

def BondConnected (ω : BondConfig) (x y : Vertex) : Prop :=
  Relation.ReflTransGen (BondOpen ω) x y

def SiteConnected (ω : SiteConfig) (x y : Vertex) : Prop :=
  ω x = true ∧ Relation.ReflTransGen (SiteOpen ω) x y

def bondCluster (ω : BondConfig) (x : Vertex) : Set Vertex :=
  {y | BondConnected ω x y}

def siteCluster (ω : SiteConfig) (x : Vertex) : Set Vertex :=
  {y | SiteConnected ω x y}

def bondInfiniteAt (x : Vertex) : Set BondConfig := {ω | (bondCluster ω x).Infinite}
def siteInfiniteAt (x : Vertex) : Set SiteConfig := {ω | (siteCluster ω x).Infinite}

noncomputable def parameter (p : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 p), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

noncomputable def bondLaw (p : ℝ) : Measure BondConfig :=
  Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false (parameter p))

noncomputable def siteLaw (p : ℝ) : Measure SiteConfig :=
  Measure.infinitePi (fun _ : Vertex => bernoulliMeasure true false (parameter p))

noncomputable def bondCritical : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < bondLaw p (bondInfiniteAt 0)}

noncomputable def siteCritical : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < siteLaw p (siteInfiniteAt 0)}

def critical_no_infinite_statement : Prop :=
  (∀ᵐ ω ∂bondLaw bondCritical, ∀ x : Vertex, (bondCluster ω x).Finite) ∧
    (∀ᵐ ω ∂siteLaw siteCritical, ∀ x : Vertex, (siteCluster ω x).Finite)

end CriticalZ3

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CriticalZ3.critical_no_infinite_statement

end Problem

/- Formalization scope, from lean/docs/213.md: The critical-percolation question asks whether an infinite cluster can remain at the threshold. The formalized result proves that, at their respective critical probabilities, nearest-neighbor bond and site percolation on $\mathbb Z^3$ almost surely have no infinite cluster. Equivalently, almost surely every vertex belongs to a finite cluster in each model. The formalization proves absence of an infinite cluster at criticality for Bernoulli bond percolation on every infinite connected locally finite quasi-transitive graph with critical probability $p_c<1$. At $p=p_c$, the probability that any infinite cluster exists is zero. The graph model permits bond multiplicities. -/
