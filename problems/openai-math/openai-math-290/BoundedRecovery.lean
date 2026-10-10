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

- problem_id: BoundedRecovery
- collection: openai-math
- question_id: openai-math:290
- source: openai-math
- source_locator: lean/ComparatorChallenges/BoundedRecovery.lean#OAI.BoundedRecovery.bounded_recovery
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Connes' bicentralizer conjecture for every type III1 factor with separable predual and every faithful normal state. More generally, for every inclusion $`N\subset M`$ of von Neumann algebras with separable preduals admitting a faithful normal conditional expectation, constructs an amenable expected subalgebra $`P\subset N`$ with $`P'\cap c(M)=N'\cap c(M)`$, resolving the relative bicentralizer conjecture. ([Lean](lean/docs/290.md)) We prove a bounded spectral recovery theorem for a von Neumann algebra with a faithful normal state whose centralizer consists only of scalars. A positive averaged squared norm for an arbitrary bounded Hilbert-space operator on shrinking modular spectral bands can be recovered on uniformly bounded algebra elements with shrinking spectral support. We apply this theorem to spectral intertwining rigidity and obtain an alternative proof of bicentralizer triviality for type III1 factors with separable predual.
- notes: OpenAI math result family 290, Relative bicentralizers and modular spectral recovery -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/290.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.BoundedRecovery.bounded_recovery
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.ModularRecovery.Main
- source_main_result: OAI.BoundedRecovery.bounded_recovery
- source_papers: preprints/Bounded-recovery-for-modular-spectral-averages-September-23-2026/Bounded-recovery-for-modular-spectral-averages-September-23-2026.pdf
- source_scope_note: lean/docs/290.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Nondegenerate spectral calculus, the closed Tomita graph, and bounded recovery. -/

universe u

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralCharacter (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I))
    (by fun_prop) 1 (by intro u; simp [Complex.norm_exp])

def halfExponentialCutoff (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (Real.exp (min (n : ℝ) u / 2) : ℂ))
    (by fun_prop) (Real.exp ((n : ℝ) / 2)) (by
      intro u
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))

structure RealSpectralCalculus (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  calculus : (BoundedContinuousFunction ℝ ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)
  nondegenerate : Dense {h : H | ∃ f : BoundedContinuousFunction ℝ ℂ,
    HasCompactSupport (f : ℝ → ℂ) ∧ ∃ k : H, calculus f k = h}

namespace RealSpectralCalculus

def unitary (D : RealSpectralCalculus H) (t : ℝ) : H →L[ℂ] H :=
  D.calculus (spectralCharacter t)

def halfGraph (D : RealSpectralCalculus H) : Set (H × H) :=
  {p | Tendsto (fun n : ℕ => D.calculus (halfExponentialCutoff n) p.1) atTop (𝓝 p.2)}

def HasSpectralSupport (D : RealSpectralCalculus H) (I : Set ℝ) (h : H) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℂ, (∀ u ∈ I, f u = 0) → D.calculus f h = 0

end RealSpectralCalculus

structure StandardModularData (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  M : VonNeumannAlgebra H
  xi : H
  norm_xi : ‖xi‖ = 1
  cyclic : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h}
  separating : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0
  D : RealSpectralCalculus H
  J : H ≃ₗᵢ⋆[ℂ] H
  conjugation : Function.Involutive J
  tomita_graph : closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ M ∧ p = (a xi, (star a) xi)} =
    {p | ∃ q : H, (p.1, q) ∈ D.halfGraph ∧ p.2 = J q}

namespace StandardModularData

def sigma (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  S.D.unitary t * a * S.D.unitary (-t)

def ScalarCentralizer (S : StandardModularData H) : Prop :=
  ∀ a : H →L[ℂ] H, a ∈ S.M → (∀ t : ℝ, S.sigma t a = a) →
    ∃ c : ℂ, a = c • (1 : H →L[ℂ] H)

end StandardModularData

def symmetricAverage (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (2 * (k : ℝ))⁻¹ * ∫ t in -(k : ℝ)..(k : ℝ), f t

def fixedMean (omega : Ultrafilter ℕ) (f : ℝ → ℝ) : ℝ :=
  Filter.limUnder (omega : Filter ℕ) (symmetricAverage f)

def RecoveryConclusion (S : StandardModularData H) (T : H →L[ℂ] H)
    (s : ℝ) (delta : ℕ → ℝ) : Prop :=
  ∃ (nj : ℕ → ℕ) (_ : StrictMono nj) (v : ℕ → (H →L[ℂ] H)) (C eta : ℝ),
    0 < eta ∧ ∀ j : ℕ, v j ∈ S.M ∧ ‖v j‖ ≤ C ∧ eta ≤ ‖T (v j S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s - 4 * delta (nj j)) (s + 4 * delta (nj j)))
        (v j S.xi)

def bounded_recovery_statement : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H) (hscalar : S.ScalarCentralizer) (omega : Ultrafilter ℕ) (hfree : (omega : Filter ℕ) ≤ Filter.atTop) (T : H →L[ℂ] H) (s : ℝ) (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n) (hdelta0 : Tendsto delta atTop (𝓝 0)) (h : ℕ → H) (hunit : ∀ n, ‖h n‖ = 1) (hband : ∀ n, S.D.HasSpectralSupport (Icc (s - delta n) (s + delta n)) (h n)) (hpositive : 0 < Filter.limsup
      (fun n => fixedMean omega (fun t => ‖T (S.D.unitary t (h n))‖ ^ 2)) atTop),
    RecoveryConclusion S T s delta

end BoundedRecovery

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.BoundedRecovery.bounded_recovery_statement.{u}

end Problem

/- Formalization scope, from lean/docs/290.md: For a faithful normal state with scalar centralizer in the stated standard-space representation, the formalized result converts positive modular spectral averages into uniformly bounded algebra elements. Given unit vectors in shrinking spectral bands around a real number $s$ and a positive limiting symmetric average for a bounded operator $T$, it finds a subsequence of bounded algebra elements whose images under $T$ stay uniformly nonzero and whose spectral bands have four times the original widths. The absolute bicentralizer conjecture is not included. -/
