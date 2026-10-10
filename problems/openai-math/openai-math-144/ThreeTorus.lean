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

- problem_id: ThreeTorus
- collection: openai-math
- question_id: openai-math:144
- source: openai-math
- source_locator: lean/ComparatorChallenges/ThreeTorus.lean#OAI.ThreeTorus.simple_lebesgue_spectrum
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the probability-preserving form of Banach's simple Lebesgue-spectrum problem within smooth dynamics. A smooth volume-preserving diffeomorphism of the standard-volume three-torus has simple Lebesgue spectrum on its entire complex mean-zero L2 space: the bilateral iterates of one real observable form an orthonormal basis of that space. ([Lean](lean/docs/144.md)) We solve the probability-preserving form of Banach's simple Lebesgue-spectrum problem in smooth dynamics. We construct a C∞ diffeomorphism of the three-torus that preserves standard volume and whose Koopman operator has simple Lebesgue spectrum on the entire mean-zero L2 space.
- notes: OpenAI math result family 144, Banach’s simple Lebesgue-spectrum problem -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/144.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ThreeTorus.simple_lebesgue_spectrum
- source_theorem_count: 1
- source_solution_module: OAI.Dynamics.ThreeTorus.Main
- source_papers: preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf
- source_scope_note: lean/docs/144.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
The torus is (ℝ/ℤ)³ with normalized product Haar measure. Smoothness means
local smooth lifts on the universal cover, for both the map and its inverse.

The almost-everywhere graph conditions are independent of representatives of
L² classes. The real generator's bilateral Koopman orbit spans the entire
complex mean-zero L² space. The spectral model is the full circle L² space
with multiplication by the first Fourier character.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

abbrev Torus := Fin 3 → UnitAddCircle
abbrev Cover := Fin 3 → ℝ

def project (x : Cover) : Torus := fun i => (x i : UnitAddCircle)

def Smooth (T : Torus → Torus) : Prop :=
  ∀ x : Cover, ∃ U : Set Cover, IsOpen U ∧ x ∈ U ∧
    ∃ F : Cover → Cover, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧
      ∀ y ∈ U, T (project y) = project (F y)

def μ : Measure Torus := Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

abbrev H : Type := Lp ℂ 2 μ

/-- The full complex subspace defined by zero Lebesgue integral. -/
def meanZero : Submodule ℂ H where
  carrier := {f | ∫ x, f x ∂μ = 0}
  zero_mem' := by
    change ∫ x, (0 : H) x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_zero ℂ 2 μ)]
    simp
  add_mem' := by
    intro f g hf hg
    change ∫ x, (f + g) x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_add f g)]
    change ∫ x, f x + g x ∂μ = 0
    rw [integral_add (MemLp.integrable (by norm_num) (Lp.memLp f))
      (MemLp.integrable (by norm_num) (Lp.memLp g))]
    change (∫ x, f x ∂μ) + (∫ x, g x ∂μ) = 0
    rw [show ∫ x, f x ∂μ = 0 from hf, show ∫ x, g x ∂μ = 0 from hg, add_zero]
  smul_mem' := by
    intro c f hf
    change ∫ x, (c • f) x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_smul c f)]
    change ∫ x, c • f x ∂μ = 0
    rw [integral_smul]
    rw [show ∫ x, f x ∂μ = 0 from hf, smul_zero]

abbrev H₀ := ↥meanZero
abbrev CircleH : Type := Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

def IsReal (f : H₀) : Prop := ∀ᵐ x ∂μ, (f.1 x).im = 0

/-- Complete simple Lebesgue spectrum, including the stated consequences. -/
def MainConclusion : Prop :=
  ∃ T : Equiv.Perm Torus,
    Smooth T ∧ Smooth T.symm ∧ MeasurePreserving T μ μ ∧
    ∃ f : H₀, IsReal f ∧
    ∃ v : ℤ → H₀,
      (∀ n : ℤ, ∀ᵐ x ∂μ, (v n).1 x = f.1 ((T ^ n) x)) ∧
      Orthonormal ℂ v ∧
      Dense (Submodule.span ℂ (Set.range v) : Set H₀) ∧
      Ergodic T μ ∧
      ∃ W : H₀ ≃ₗᵢ[ℂ] CircleH,
        ∀ g : H₀, ∃ h : H₀,
          (∀ᵐ x ∂μ, h.1 x = g.1 (T x)) ∧
          (∀ᵐ z ∂(AddCircle.haarAddCircle (T := (1 : ℝ))),
            W h z = fourier 1 z * W g z)

def simple_lebesgue_spectrum_statement : Prop :=
  MainConclusion

end ThreeTorus

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ThreeTorus.simple_lebesgue_spectrum_statement

end Problem

/- Formalization scope, from lean/docs/144.md: Banach's simple Lebesgue-spectrum problem asks for a probability-preserving transformation with simple Lebesgue spectrum on its mean-zero $L^2$ space. The formalization constructs a smooth volume-preserving diffeomorphism of the three-torus with this property. It gives a real-valued cyclic vector whose integer iterates form an orthonormal basis of the entire mean-zero space, and an isometric identification under which the Koopman operator becomes multiplication by the coordinate function on the circle. The transformation is also ergodic. -/
