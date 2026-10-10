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

- problem_id: LipschitzHilbert
- collection: openai-math
- question_id: openai-math:083
- source: openai-math
- source_locator: lean/ComparatorChallenges/LipschitzHilbert.lean#OAI.LipschitzHilbert.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves a uniform strong L2 bound for the planar Hilbert transform along any Lipschitz unit vector field, at integration lengths bounded by an absolute multiple of its reciprocal Lipschitz constant. The estimate is uniform over inner truncations and yields an L2-bounded principal-value operator, establishing Stein's weak-type conjecture at this short scale. ([Lean](lean/docs/083.md)) We prove a uniform L2 bound for the Hilbert transform along a Lipschitz unit vector field in the plane, with integration restricted to a fixed absolute multiple of the reciprocal Lipschitz seminorm. The bound is uniform in the inner truncation and holds for fields depending on both coordinates. This gives an affirmative answer to Stein's weak-$`(2,2)`$ conjecture.
- notes: OpenAI math result family 083, Hilbert transforms along Lipschitz directions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/083.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LipschitzHilbert.main OAI.LipschitzHilbert.uniform_truncation
- source_theorem_count: 2
- source_solution_module: OAI.Analysis.LipschitzHilbert.Main
- source_papers: preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf
- source_scope_note: lean/docs/083.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

/- Use the normed-field structure on ℂ for real scalar multiplication. -/
attribute [-instance] instCommCStarAlgebraComplex

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev DirectionPlane := EuclideanSpace ℝ (Fin 2)

def sample (v : DirectionPlane → DirectionPlane) (t : ℝ) (x : DirectionPlane) :
    DirectionPlane := x - t • v x

/-- The symmetrized form of the hard-truncated directional integral. -/
def shortTransform (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  ∫ t in ε..a, t⁻¹ • (f (sample v t x) - f (sample v (-t) x))

def directionalKernel (v : DirectionPlane → DirectionPlane)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) (t : ℝ) : ℂ :=
  t⁻¹ • f (sample v t x)

/-- The two hard-cutoff intervals in the directional Hilbert transform. -/
def twoSidedTruncation (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  (∫ t in -a..-ε, directionalKernel v f x t) +
    ∫ t in ε..a, directionalKernel v f x t

/-- The symmetric quotient extended continuously at zero for smooth inputs. -/
def smoothPrincipalValue (v : DirectionPlane → DirectionPlane) (a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  let g := fun t : ℝ => f (sample v t x)-f (sample v (-t) x)
  ∫ t in (0:ℝ)..a, Function.update (fun t => t⁻¹ • g t) 0 (deriv g 0) t

attribute [instance] instCommCStarAlgebraComplex

def ShortHilbertConclusion (a : ℝ) (C : ℝ≥0) : Prop :=
  ∀ v : Plane → Plane, LipschitzWith 1 v → (∀ x, ‖v x‖=1) →
    (∀ epsilon : ℝ, 0<epsilon → epsilon<a → ∀ f : SchwartzMap Plane ℂ,
      eLpNorm (twoSidedTruncation v epsilon a f) 2 volume≤C*eLpNorm f 2 volume) ∧
    (∀ f : SchwartzMap Plane ℂ,
      eLpNorm (smoothPrincipalValue v a f) 2 volume≤C*eLpNorm f 2 volume) ∧
    (∀ f : SchwartzMap Plane ℂ, ∀ level : ℝ≥0∞, level≠0 → level≠∞ →
      volume {x | level<‖smoothPrincipalValue v a f x‖ₑ}≤
        level⁻¹^2*((C:ℝ≥0∞)*eLpNorm f 2 volume)^2) ∧
    (∀ epsilon : ℝ, 0<epsilon → epsilon<a →
      ∃ T : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] Lp ℂ 2 volume,
        ‖T‖≤C ∧ ∀ f : SchwartzMap Plane ℂ,
          (T (f.toLp 2 volume) : Plane → ℂ)=ᵐ[volume] twoSidedTruncation v epsilon a f) ∧
    (∃ T : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] Lp ℂ 2 volume,
      ‖T‖≤C ∧ ∀ f : SchwartzMap Plane ℂ,
        (T (f.toLp 2 volume) : Plane → ℂ)=ᵐ[volume] smoothPrincipalValue v a f)

/-- Uniform hard truncation, principal-value and weak-(2,2) estimates,
with bounded L² extensions for all Lipschitz unit vector fields. -/
def main_statement : Prop :=
  ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C

/-- The same uniform estimate at the reciprocal-Lipschitz truncation scale. -/
def uniform_truncation_statement : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖)

end LipschitzHilbert

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LipschitzHilbert.main_statement ∧
  _root_.OAI.LipschitzHilbert.uniform_truncation_statement

end Problem

/- Formalization scope, from lean/docs/083.md: The formalization proves uniform $L^2$ bounds for short Hilbert transforms along Lipschitz unit vector fields in the plane, including fields depending on both coordinates. For Lipschitz constant $K>0$, every hard truncation with $0<\varepsilon\le R\le1/(10^6K)$ has one universal $L^2$ bound on Schwartz functions, independent of the inner cutoff. At a fixed short scale for $1$-Lipschitz fields, the formalization also gives principal-value and weak-$(2,2)$ estimates and bounded extensions to all of $L^2$. These results establish the stated short-scale form of Stein's question. -/
