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

- problem_id: CayleyPercolation
- collection: openai-math
- question_id: openai-math:214
- source: openai-math
- source_locator: lean/ComparatorChallenges/CayleyPercolation.lean#OAI.Percolation.arbitrary_cayley
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves $`p_c\lt p_u`$ for Bernoulli bond percolation on every infinite connected locally finite nonamenable quasi-transitive graph, resolving the Benjamini–Schramm nonuniqueness conjecture. Thus there is a nonempty range of probabilities with infinitely many infinite clusters. A stronger operator bound also establishes the critical triangle condition. ([Lean](lean/docs/214.md)) We prove the bond-percolation nonuniqueness conjecture of Benjamini and Schramm: every infinite connected, locally finite, nonamenable quasi-transitive graph has a nonempty interval of parameters for which Bernoulli bond percolation almost surely has infinitely many infinite clusters. We also prove Hutchcroft's stronger operator-threshold conjecture, establishing $`p_c\lt p_{2\to2}\le p_u`$.
- notes: OpenAI math result family 214, The Benjamini–Schramm nonuniqueness conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/214.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Percolation.arbitrary_cayley
- source_theorem_count: 1
- source_solution_module: OAI.Probability.UnimodularPercolation.CayleyMain
- source_papers: preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf
- source_scope_note: lean/docs/214.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Nonuniqueness of Bernoulli bond percolation on arbitrary Cayley graphs. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

abbrev BondGraph (V : Type u) (E : Type v) := E → Sym2 V

def Conn (G : BondGraph V E) (ω : Set E) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ e ∈ ω, G e = s(a, b)) x y

def cluster (G : BondGraph V E) (ω : Set E) (x : V) : Set V :=
  {y | Conn G ω x y}

def infiniteClusters (G : BondGraph V E) (ω : Set E) : Set (Set V) :=
  {C | C.Infinite ∧ ∃ x, C = cluster G ω x}

noncomputable def law (p : unitInterval) : Measure (Set E) :=
  setBernoulli Set.univ p

noncomputable def pc (G : BondGraph V E) : unitInterval :=
  sInf {p | 0 < law p {ω | (infiniteClusters G ω).Nonempty}}

noncomputable def pu (G : BondGraph V E) : unitInterval :=
  sInf {p | law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 1}

noncomputable def twoPoint (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  (law p {ω | Conn G ω x y}).toReal

noncomputable abbrev Hilbert (V : Type u) := lp (fun _ : V => ℂ) 2

noncomputable def HasKernel [DecidableEq V]
    (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ x y, (A (lp.single 2 y (1 : ℂ))) x = (twoPoint G p x y : ℂ)

noncomputable def OperatorBounded (G : BondGraph V E) (p : unitInterval) : Prop := by
  classical
  exact ∃ A : Hilbert V →L[ℂ] Hilbert V, HasKernel G p A

noncomputable def ptwo (G : BondGraph V E) : unitInterval :=
  sSup {p | OperatorBounded G p}

noncomputable def labelLaw : Measure (E → unitInterval) :=
  Measure.infinitePi (fun _ => (volume : Measure unitInterval))

def openEdges (labels : E → unitInterval) (p : unitInterval) : Set E :=
  {e | labels e ≤ p}

noncomputable def AmenableGroup (Λ : Type u) [Group Λ] : Prop := by
  classical
  exact ∀ K : Finset Λ, ∀ ε : ℝ, 0 < ε → ∃ A : Finset Λ, A.Nonempty ∧
    ∀ g ∈ K, (((A.image (fun x => x * g)) \ A).card : ℝ) < ε * A.card

def CayleyEdge {Λ : Type u} [Group Λ] (S : Finset Λ) :=
  {e : Sym2 Λ // ∃ x : Λ, ∃ s ∈ S, e = s(x, x * s)}

def cayleyGraph {Λ : Type u} [Group Λ] (S : Finset Λ) :
    BondGraph Λ (CayleyEdge S) := Subtype.val

def arbitrary_cayley_statement : Prop :=
  ∀ {Λ : Type u} [Group Λ] [Group.FG Λ] (hna : ¬ AmenableGroup Λ) (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set Λ) = ⊤) (h1 : 1 ∉ S),
    OperatorBounded (cayleyGraph S) (pc (cayleyGraph S)) ∧
    pc (cayleyGraph S) < ptwo (cayleyGraph S) ∧
    ptwo (cayleyGraph S) ≤ pu (cayleyGraph S) ∧
    (∃ p₁ p₂ : unitInterval, pc (cayleyGraph S) < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧
      ∀ᵐ labels ∂(labelLaw : Measure (CayleyEdge S → unitInterval)),
        ∀ p ∈ Set.Icc p₁ p₂, (infiniteClusters (cayleyGraph S) (openEdges labels p)).Infinite) ∧
    (∀ p : unitInterval, pc (cayleyGraph S) < p → p < pu (cayleyGraph S) →
      ∀ᵐ ω ∂law p, (infiniteClusters (cayleyGraph S) ω).Infinite)

end Percolation

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.Percolation.arbitrary_cayley_statement.{u}

end Problem

/- Formalization scope, from lean/docs/214.md: The formalization proves the nonuniqueness phase conjecture for Bernoulli bond percolation on infinite connected locally finite nonamenable quasi-transitive graphs. It establishes $p_c<p_{2\to2}\le p_u$ and a common nonempty coupled interval with infinitely many infinite clusters almost surely. For Cayley graphs, the result holds for every finite symmetric generating set of a nonamenable finitely generated group and every $p\in(p_c,p_u)$. The selected critical estimates include a finite triangle diagram, susceptibility of order $(p_c-p)^{-1}$, percolation probability of order $p-p_c$, cluster-volume tail of order $n^{-1/2}$, and intrinsic and extrinsic radius tails of order $n^{-1}$. Connection probabilities decay exponentially below $p_{2\to2}$. -/
