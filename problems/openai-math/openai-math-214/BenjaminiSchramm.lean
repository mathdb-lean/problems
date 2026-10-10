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

- problem_id: BenjaminiSchramm
- collection: openai-math
- question_id: openai-math:214
- source: openai-math
- source_locator: lean/ComparatorChallenges/BenjaminiSchramm.lean#OAI.Percolation.BenjaminiSchramm.full_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves $`p_c\lt p_u`$ for Bernoulli bond percolation on every infinite connected locally finite nonamenable quasi-transitive graph, resolving the Benjamini–Schramm nonuniqueness conjecture. Thus there is a nonempty range of probabilities with infinitely many infinite clusters. A stronger operator bound also establishes the critical triangle condition. ([Lean](lean/docs/214.md)) We prove the bond-percolation nonuniqueness conjecture of Benjamini and Schramm: every infinite connected, locally finite, nonamenable quasi-transitive graph has a nonempty interval of parameters for which Bernoulli bond percolation almost surely has infinitely many infinite clusters. We also prove Hutchcroft's stronger operator-threshold conjecture, establishing $`p_c\lt p_{2\to2}\le p_u`$.
- notes: OpenAI math result family 214, The Benjamini–Schramm nonuniqueness conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/214.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Percolation.BenjaminiSchramm.full_main OAI.Percolation.BenjaminiSchramm.cayley_main OAI.Percolation.BenjaminiSchramm.critical_laws
- source_theorem_count: 3
- source_solution_module: OAI.Probability.BenjaminiSchramm.Main
- source_papers: preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf
- source_scope_note: lean/docs/214.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

abbrev BondGraph (V : Type u) (E : Type v) := E → Sym2 V

def Adj (G : BondGraph V E) (x y : V) : Prop := ∃ e, G e = s(x, y)

def LocallyFinite (G : BondGraph V E) : Prop := ∀ x, {e | x ∈ G e}.Finite

def Connected (G : BondGraph V E) : Prop :=
  ∀ x y, Relation.ReflTransGen (Adj G) x y

def IsAut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E) : Prop :=
  ∀ e, G (b e) = (G e).map a

def QuasiTransitive (G : BondGraph V E) : Prop :=
  ∃ representatives : Finset V, ∀ x, ∃ o ∈ representatives,
    ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ a o = x

def vertexBoundary (G : BondGraph V E) (A : Finset V) : Set V :=
  {y | y ∉ A ∧ ∃ x ∈ A, Adj G x y}

noncomputable def hV (G : BondGraph V E) : ℝ :=
  sInf {r | ∃ A : Finset V, A.Nonempty ∧
    r = (vertexBoundary G A).ncard / (A.card : ℝ)}

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

noncomputable def operatorNorm (G : BondGraph V E) (p : unitInterval) : ℝ≥0∞ := by
  classical
  exact sInf {r | ∃ A : Hilbert V →L[ℂ] Hilbert V,
    HasKernel G p A ∧ r = ENNReal.ofReal ‖A‖}

noncomputable def ptwo (G : BondGraph V E) : unitInterval :=
  sSup {p | OperatorBounded G p}

noncomputable def labelLaw : Measure (E → unitInterval) :=
  Measure.infinitePi (fun _ => (volume : Measure unitInterval))

def openEdges (labels : E → unitInterval) (p : unitInterval) : Set E :=
  {e | labels e ≤ p}

def MainConclusion (G : BondGraph V E) : Prop :=
  (sSup {r | ∃ p : unitInterval, p < pc G ∧ r = operatorNorm G p} =
    operatorNorm G (pc G)) ∧
  operatorNorm G (pc G) < ⊤ ∧
  pc G < ptwo G ∧ ptwo G ≤ pu G ∧
  ∃ p₁ p₂ : unitInterval, pc G < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      ∀ p ∈ Set.Icc p₁ p₂, (infiniteClusters G (openEdges labels p)).Infinite

end Percolation

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable

def openSimpleGraph (G : BondGraph V E) (ω : Set E) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e ∈ ω, G e = s(x,y)
  symm := ⟨by
    rintro x y ⟨hxy, e, he, h⟩
    exact ⟨hxy.symm, e, he, h.trans (Sym2.eq_swap ..)⟩⟩
  loopless := ⟨by simp⟩

end Percolation

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def susceptibility (G : BondGraph V E) (p : unitInterval) (x : V) : ℝ :=
  ∑' y, twoPoint G p x y

end Percolation

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation.BenjaminiSchramm
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq

noncomputable def triangleDiagram (G : BondGraph V E) (p : unitInterval) (x : V) : ℝ≥0∞ :=
  ∑' ab : V × V, ENNReal.ofReal
    (twoPoint G p x ab.1 * twoPoint G p ab.1 ab.2 * twoPoint G p ab.2 x)

noncomputable def graphDistance (G : BondGraph V E) (x y : V) : ℕ :=
  (openSimpleGraph G Set.univ).dist x y

def ExponentialDecay (G : BondGraph V E) (p : unitInterval) : Prop :=
  ∃ A a : ℝ, 0 < A ∧ 0 < a ∧ ∀ x y,
    twoPoint G p x y ≤ A * Real.exp (-a * graphDistance G x y)

noncomputable def pexp (G : BondGraph V E) : unitInterval :=
  sSup {p | ExponentialDecay G p}

def PowerTail (f : ℕ → ℝ) (exponent : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 0 < n →
    c * (n : ℝ) ^ (-exponent) ≤ f n ∧ f n ≤ C * (n : ℝ) ^ (-exponent)

def volumeEvent (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | (n : ℕ∞) ≤ (cluster G ω x).encard}

def intrinsicRadiusEvent (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ y ∈ cluster G ω x, n ≤ (openSimpleGraph G ω).dist x y}

def extrinsicRadiusEvent (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ y ∈ cluster G ω x, n ≤ graphDistance G x y}

noncomputable def criticalTail (G : BondGraph V E)
    (A : V → ℕ → Set (Set E)) (x : V) (n : ℕ) : ℝ :=
  (law (pc G) (A x n)).toReal

def CriticalTailLaws (G : BondGraph V E) : Prop :=
  ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2) ∧
    PowerTail (criticalTail G (intrinsicRadiusEvent G) x) 1 ∧
    PowerTail (criticalTail G (extrinsicRadiusEvent G) x) 1

def SusceptibilityLaw (G : BondGraph V E) : Prop :=
  ∀ x, ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
    ∀ p : unitInterval, p < pc G → (pc G : ℝ) - p < δ →
      c / ((pc G : ℝ) - p) ≤ susceptibility G p x ∧
      susceptibility G p x ≤ C / ((pc G : ℝ) - p)

noncomputable def percolationProbability (G : BondGraph V E) (p : unitInterval)
    (x : V) : ℝ := (law p {ω | (cluster G ω x).Infinite}).toReal

def PercolationProbabilityLaw (G : BondGraph V E) : Prop :=
  ∀ x, ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
    ∀ p : unitInterval, pc G < p → (p : ℝ) - pc G < δ →
      c * ((p : ℝ) - pc G) ≤ percolationProbability G p x ∧
      percolationProbability G p x ≤ C * ((p : ℝ) - pc G)

end Percolation.BenjaminiSchramm

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation.BenjaminiSchramm
universe u v
variable {V : Type u} {E : Type v}

def CriticalLawsConclusion (G : BondGraph V E) : Prop :=
  (∀ x, triangleDiagram G (pc G) x ≤ operatorNorm G (pc G) ^ 3 ∧
    triangleDiagram G (pc G) x < ⊤) ∧
  SusceptibilityLaw G ∧ PercolationProbabilityLaw G ∧ CriticalTailLaws G ∧
  (pc G < ptwo G ∧ ptwo G ≤ pexp G) ∧
  ∀ p : unitInterval, p < ptwo G → ExponentialDecay G p

end Percolation.BenjaminiSchramm

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation.BenjaminiSchramm
universe u
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.decEq

abbrev CayleyEdge (S : Finset Λ) := (SimpleGraph.mulCayley (S : Set Λ)).edgeSet

def cayleyBond (S : Finset Λ) : BondGraph Λ (CayleyEdge S) := Subtype.val

def FolnerAmenable (Λ : Type u) [Group Λ] : Prop :=
  ∀ K : Finset Λ, ∀ ε : ℝ, 0 < ε → ∃ A : Finset Λ, A.Nonempty ∧
    ∀ k ∈ K, (((A.image (fun x => x * k)) \ A).card : ℝ) < ε * A.card

end Percolation.BenjaminiSchramm

namespace Percolation.BenjaminiSchramm

universe u v

/-- Critical operator boundedness, the threshold gap, and simultaneous nonuniqueness. -/
def full_main_statement : Prop :=
  ∀ {V : Type u} {E : Type v} [Infinite V] (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G) (hh : 0 < hV G),
    MainConclusion G

/-- Critical mean-field laws and uniform exponential connectivity below the operator threshold. -/
def critical_laws_statement : Prop :=
  ∀ {V : Type u} {E : Type v} [Infinite V] (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G) (hh : 0 < hV G),
    CriticalLawsConclusion G

/-- Nonuniqueness for every prescribed finite symmetric Cayley generating set. -/
def cayley_main_statement : Prop :=
  ∀ {Λ : Type u} [Group Λ] (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (_hone : 1 ∉ S) (hgen : Subgroup.closure (S : Set Λ) = ⊤) (hna : ¬ FolnerAmenable Λ),
    OperatorBounded (cayleyBond S) (pc (cayleyBond S)) ∧
      MainConclusion (cayleyBond S) ∧
      ∀ p : unitInterval, pc (cayleyBond S) < p → p < pu (cayleyBond S) →
        ∀ᵐ ω ∂law p, (infiniteClusters (cayleyBond S) ω).Infinite

end Percolation.BenjaminiSchramm

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u, v} : Prop :=
  _root_.OAI.Percolation.BenjaminiSchramm.full_main_statement.{u, v} ∧
  _root_.OAI.Percolation.BenjaminiSchramm.critical_laws_statement.{u, v} ∧
  _root_.OAI.Percolation.BenjaminiSchramm.cayley_main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/214.md: The formalization proves the nonuniqueness phase conjecture for Bernoulli bond percolation on infinite connected locally finite nonamenable quasi-transitive graphs. It establishes $p_c<p_{2\to2}\le p_u$ and a common nonempty coupled interval with infinitely many infinite clusters almost surely. For Cayley graphs, the result holds for every finite symmetric generating set of a nonamenable finitely generated group and every $p\in(p_c,p_u)$. The selected critical estimates include a finite triangle diagram, susceptibility of order $(p_c-p)^{-1}$, percolation probability of order $p-p_c$, cluster-volume tail of order $n^{-1/2}$, and intrinsic and extrinsic radius tails of order $n^{-1}$. Connection probabilities decay exponentially below $p_{2\to2}$. -/
