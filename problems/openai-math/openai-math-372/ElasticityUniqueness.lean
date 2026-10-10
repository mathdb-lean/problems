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

- problem_id: ElasticityUniqueness
- collection: openai-math
- question_id: openai-math:372
- source: openai-math
- source_locator: lean/ComparatorChallenges/ElasticityUniqueness.lean#OAI.Elasticity.global_uniqueness
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that full static boundary displacement-to-traction data determine both smooth real Lamé moduli on every bounded connected smooth domain in ℝ3, provided μ &gt; 0 and $`3\lambda+2\mu\gt 0`$ on the closure. Neither analyticity, proximity to constant coefficients nor prior knowledge near the boundary is required. ([Lean](lean/docs/372.md)) We prove that the full static displacement-to-traction map uniquely determines both real smooth Lamé moduli on every bounded connected smooth domain in ℝ3, provided μ &gt; 0 and $`3\lambda+2\mu\gt 0`$ on the closure. This resolves the smooth three-dimensional isotropic elastic Calderón uniqueness problem under these positivity assumptions.
- notes: OpenAI math result family 372, Global uniqueness in smooth isotropic elasticity -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/372.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Elasticity.global_uniqueness
- source_theorem_count: 1
- source_solution_module: OAI.MathematicalPhysics.Elasticity.Uniqueness
- source_papers: preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf
- source_scope_note: lean/docs/372.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
# Global uniqueness for smooth isotropic elasticity

The physical Dirichlet-to-Neumann pairing acts on the variational trace
quotient. Its quotient norm is not identified here with boundary-chart
fractional Sobolev norms.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Elasticity

abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev V := X

def coordVector (i : Fin 3) : X := EuclideanSpace.single i 1

def SmoothBoundary (Ω : Set X) : Prop :=
  ∀ x ∈ frontier Ω, ∃ e : OpenPartialHomeomorph X X,
    x ∈ e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
    e x 0 = 0 ∧
    ∀ y ∈ e.source, y ∈ Ω ↔ 0 < e y 0

def Domain (Ω : Set X) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧ SmoothBoundary Ω

def SmoothUpTo (Ω : Set X) (f : X → ℝ) : Prop :=
  ∃ U : Set X, IsOpen U ∧ closure Ω ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U

def Admissible (Ω : Set X) (lam mu : X → ℝ) : Prop :=
  SmoothUpTo Ω lam ∧ SmoothUpTo Ω mu ∧
    ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x

abbrev Ambient (Ω : Set X) :=
  Lp V 2 (volume.restrict Ω) × (Fin 3 → Lp V 2 (volume.restrict Ω))

def coordDeriv (f : X → V) (i : Fin 3) (x : X) : V :=
  fderiv ℝ f x (coordVector i)

def SmoothJets (Ω : Set X) : Set (Ambient Ω) :=
  {j | ∃ (f : X → V) (hf : MemLp f 2 (volume.restrict Ω))
      (hd : ∀ i, MemLp (coordDeriv f i) 2 (volume.restrict Ω)),
    ContDiff ℝ (⊤ : ℕ∞) f ∧
    j.1 = hf.toLp f ∧ j.2 = fun i => (hd i).toLp (coordDeriv f i)}

def TestJets (Ω : Set X) : Set (Ambient Ω) :=
  {j | ∃ (f : X → V) (hf : MemLp f 2 (volume.restrict Ω))
      (hd : ∀ i, MemLp (coordDeriv f i) 2 (volume.restrict Ω)),
    ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω ∧
    j.1 = hf.toLp f ∧ j.2 = fun i => (hd i).toLp (coordDeriv f i)}

abbrev H1 (Ω : Set X) := {j : Ambient Ω // j ∈ closure (SmoothJets Ω)}

def HasZeroTrace (Ω : Set X) (u : H1 Ω) : Prop :=
  u.val ∈ closure (TestJets Ω)

def SameTrace (Ω : Set X) (u v : H1 Ω) : Prop :=
  u.val - v.val ∈ closure (TestJets Ω)

abbrev BoundaryData (Ω : Set X) := Quot (SameTrace Ω)

def trace (Ω : Set X) (u : H1 Ω) : BoundaryData Ω := Quot.mk _ u

def div (Ω : Set X) (u : H1 Ω) (x : X) : ℝ :=
  ∑ i, (u.val.2 i x) i

def strain (Ω : Set X) (u : H1 Ω) (x : X) (i j : Fin 3) : ℝ :=
  ((u.val.2 j x) i + (u.val.2 i x) j) / 2

def energy (Ω : Set X) (lam mu : X → ℝ) (u v : H1 Ω) : ℝ :=
  ∫ x, (lam x * div Ω u x * div Ω v x +
    2 * mu x * ∑ i, ∑ j, strain Ω u x i j * strain Ω v x i j)
    ∂(volume.restrict Ω)

def WeakSolution (Ω : Set X) (lam mu : X → ℝ) (u : H1 Ω) : Prop :=
  ∀ v : H1 Ω, HasZeroTrace Ω v → energy Ω lam mu u v = 0

def dirichletSolution (Ω : Set X) (lam mu : X → ℝ)
    (f : BoundaryData Ω) : H1 Ω := by
  classical
  exact if h : ∃ u : H1 Ω, trace Ω u = f ∧ WeakSolution Ω lam mu u
  then Classical.choose h
  else f.out

def DN (Ω : Set X) (lam mu : X → ℝ) : BoundaryData Ω → BoundaryData Ω → ℝ :=
  fun f g => energy Ω lam mu (dirichletSolution Ω lam mu f) g.out

def MainClaim : Prop :=
  ∀ (Ω : Set X), Domain Ω →
  ∀ (lam₁ mu₁ lam₂ mu₂ : X → ℝ),
    Admissible Ω lam₁ mu₁ → Admissible Ω lam₂ mu₂ →
    DN Ω lam₁ mu₁ = DN Ω lam₂ mu₂ →
    (∀ x ∈ Ω, lam₁ x = lam₂ x) ∧ (∀ x ∈ Ω, mu₁ x = mu₂ x)

def global_uniqueness_statement : Prop :=
  MainClaim

end Elasticity

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Elasticity.global_uniqueness_statement

end Problem

/- Formalization scope, from lean/docs/372.md: The formalization proves global uniqueness in the three-dimensional static isotropic elasticity inverse problem. On a bounded connected smooth domain, let two pairs of smooth real Lamé moduli satisfy $\mu>0$ and $3\lambda+2\mu>0$ on the closure. If their full displacement-to-traction maps agree, then both Lamé moduli agree throughout the domain. The selected statement is uniqueness; it does not supply a reconstruction algorithm. -/
