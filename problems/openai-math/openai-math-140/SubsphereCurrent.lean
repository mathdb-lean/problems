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

- problem_id: SubsphereCurrent
- collection: openai-math
- question_id: openai-math:140
- source: openai-math
- source_locator: lean/ComparatorChallenges/SubsphereCurrent.lean#OAI.SubsphereCurrent.full_current_main_scope
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For fixed A &gt; 0, a one-pass learner with $`Ad^2`$ persistent bits needs $`\Omega_A(d\log(1/\epsilon))`$ noiseless Gaussian samples to recover a unit vector to angular error $`0\lt \epsilon\le1/10`$ with probability 2/3, uniformly in accuracy for large d. Computation and randomized updates are unrestricted, but output uses only the terminal state, stopping index and fresh randomness. ([Lean](lean/docs/140.md)) For every fixed A &gt; 0, a learner that retains at most $`Ad^2`$ bits between fresh exact Gaussian linear measurements needs $`\Omega_A(d\log(1/\epsilon))`$ measurements to estimate a uniformly random unit vector to angular error at most ϵ, for any $`0\lt \epsilon\le 1/10`$, with probability at least 2/3. The constant is absolute for $`o(d^2)`$ memory. For a signal with density bounded by L relative to uniform probability on $`S^{d-1}`$, we bound the information in a finite message W formed from exact Gaussian measurements, conditional on an independent projection revealed only to the analyst. For explicit row counts proportional to d, the bound is $`O(H(W)/d+d+\log(2+\log L))`$. Consequently, a finite-state learner with $`o(d^2)`$ persistent bits and a deterministic sample horizon needs $`\Omega(d\log(1/\epsilon))`$ fresh noiseless Gaussian measurements for constant-probability angular accuracy $`0\lt \epsilon\le1/10`$ under the uniform spherical prior. For the image of a uniform cube under a spherical coordinate map, we prove that finite messages from t blocks of $`\Theta(d)`$ exact Gaussian measurements reveal only $`O_A(dt)`$ information when each message has at most $`\exp(Ad^2)`$ values, for fixed A. The same bound holds when each message is supplemented with a nested cell that restores the required geometric spread. We prove moment estimates for exact random projections of finite measures whose mass is controlled on Euclidean balls, and derive positive domination by countable sums of spherical cap measures. For learners with $`M=o(d^2)`$ bits of memory, these estimates give three proofs that uniform-sphere average success at least 2/3 at angular accuracy $`0\lt \epsilon\le1/10`$ requires $`\Omega(d\log(1/\epsilon))`$ noiseless Gaussian observations. The three proofs keep their different stopping and accuracy costs explicit. Replacing the Gaussian rows used to select a finite message by independent rows increases the remaining conditional information by at most $`Cd`$, for a uniform spherical signal, message entropy at most d2, and the specified row dimensions proportional to d. As an application, we prove that learners with $`M=o(d^2)`$ persistent bits need $`T=\Omega(d\log(1/\epsilon))`$ exact observations to attain uniform-sphere angular success at least 3/5, for $`0\lt \epsilon\le1/10`$ and a deterministic finite horizon. Let a finite-state streaming learner estimate a uniformly random unit vector from independent exact Gaussian linear measurements. We prove that $`o(d^2)`$ bits of persistent memory and angular success probability at least 2/3 require at least $`2^{-16}d\log_2(1/\epsilon)`$ samples for all sufficiently large d, uniformly for $`0\lt \epsilon\le1/10`$. The proof conditions each batch on its observed projection and controls the resulting random residual subsphere.
- notes: OpenAI math result family 140, Memory–sample lower bounds for noiseless Gaussian regression -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/140.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SubsphereCurrent.full_current_main_scope
- source_theorem_count: 1
- source_solution_module: OAI.Probability.Subsphere.Main
- source_main_result: OAI.SubsphereCurrent.full_current_main_scope
- source_papers: preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf preprints/Projection-moments-positive-cap-domination-and-Riesz-estimates-on-the-sphere-September-27-2026/paper.pdf preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf preprints/Subsphere-methods-for-memory-sample-lower-bounds-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf
- source_scope_note: lean/docs/140.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
abbrev State (M : ℕ) := Fin (2 ^ M)
abbrev Samples (d T : ℕ) := Fin T → Vector d

def uniformSphere (d : ℕ) : Measure (UnitSphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ

def sampleLaw (d T : ℕ) : Measure (Samples d T) :=
  Measure.pi fun _ => stdGaussian (Vector d)

def observationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

structure KernelLearner (d M T : ℕ) where
  initial : PMF (Bool × State M)
  transition : ℕ → State M → (Vector d × ℝ) → PMF (Bool × State M)
  output : ℕ → State M → Measure (UnitSphere d)
  output_probability : ∀ t q, IsProbabilityMeasure (output t q)

namespace KernelLearner
abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)

def tagged (M t : ℕ) (a : Bool × State M) : RunStatus M :=
  if a.1 then .inr (t, a.2) else .inl a.2

def run {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) : ℕ → PMF (RunStatus M)
  | 0 => L.initial.map (tagged M 0)
  | n + 1 => (L.run s x n).bind fun status =>
      match status with
      | .inr done => PMF.pure (.inr done)
      | .inl q => if hn : n < T then
          (L.transition (n + 1) q (x ⟨n, hn⟩, ⟪x ⟨n, hn⟩, s.val⟫)).map (tagged M (n + 1))
        else PMF.pure (.inl q)

def terminal {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) : PMF (ℕ × State M) :=
  (L.run s x T).map fun status =>
    match status with
    | .inl q => (T, q)
    | .inr done => done

def estimateLaw {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) : Measure (UnitSphere d) :=
  (L.terminal s x).toMeasure.bind fun a => L.output a.1 a.2

def angularError {d : ℕ} (s u : UnitSphere d) : ℝ :=
  Real.arccos ⟪u.val, s.val⟫

def conditionalSuccess {d M T : ℕ} (L : KernelLearner d M T) (ε : ℝ)
    (s : UnitSphere d) (x : Samples d T) : ℝ≥0∞ :=
  L.estimateLaw s x {u | angularError s u ≤ ε}

def CompletedRules {d M T : ℕ} (L : KernelLearner d M T) : Prop :=
  ∀ t q dest, AEMeasurable (fun obs => L.transition t q obs dest) (observationReference d)

end KernelLearner

structure SeededLearner (d M T : ℕ) (Ω : Type u) where
  rules : Ω → KernelLearner d M T

namespace SeededLearner

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) : Prop where
  completed_rules : ∀ᵐ ω ∂ρ, (L.rules ω).CompletedRules
  fixed_experiment : ∀ s ε, AEMeasurable
    (fun z : Ω × Samples d T => (L.rules z.1).conditionalSuccess ε s z.2)
    (ρ.prod (sampleLaw d T))
  uniform_experiment : ∀ ε, AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) =>
      (L.rules z.2.1).conditionalSuccess ε z.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

def success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  ∫⁻ z : Ω × Samples d T, (L.rules z.1).conditionalSuccess ε s z.2
    ∂(ρ.prod (sampleLaw d T))

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : SeededLearner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × (Ω × Samples d T),
    (L.rules z.2.1).conditionalSuccess ε z.1 z.2.2
      ∂((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
end SeededLearner

def ExplicitPrecision : Prop :=
  ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : SeededLearner d (M d) T Ω, L.Admissible ρ →
    ((2 / 3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε ∨
      ∀ s, (2 / 3 : ℝ≥0∞) ≤ L.success ρ ε s) →
    (2 : ℝ)⁻¹ ^ 16 * (d : ℝ) * Real.logb 2 (1 / ε) ≤ (T : ℝ)
end SubsphereCurrent
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Sphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

def sphereLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Sphere E) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

structure Test (d n : ℕ) where
  space : Submodule ℝ (Vector d)
  dimension : Module.finrank ℝ space = n
  center : Vector d
  perpendicular : center ∈ spaceᗮ
  radius : ℝ
  radius_positive : 0 < radius
  unit : ‖center‖^2 + radius^2 = 1

def Test.point {d n : ℕ} (A : Test d n) (s : Sphere A.space) : Vector d :=
  A.center + A.radius • s.val.val

end SubsphereCurrent.Affine
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe v
namespace SubsphereCurrent.Weighted
abbrev Vector (d : ℕ) := Affine.Vector d
abbrev Sphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
abbrev Rows (d k : ℕ) := Fin k → Vector d
abbrev Observation (d k : ℕ) := Rows d k × (Fin k → ℝ)

def onTest {d n : ℕ} (A : Affine.Test d n) (s : Affine.Sphere A.space) : Sphere d := by
  refine ⟨A.point s,mem_sphere_zero_iff_norm.mpr ?_⟩
  have hs : ‖(s.val : Vector d)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  have ho : ⟪A.center, (s.val : Vector d)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal s.val.property A.perpendicular
  have hz : ‖A.point s‖^2 = 1 := by
    rw [Affine.Test.point,norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.radius_positive,hs,mul_one]
    nlinarith [A.unit]
  nlinarith [norm_nonneg (A.point s)]

def norm (d n : ℕ) (g : Sphere d → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ A : Affine.Test d n, (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
    ∫⁻ s : Affine.Sphere A.space, g (onTest A s) ∂Affine.sphereLaw A.space

def blockInput {d k : ℕ} {V : Type*} [Fintype V]
    (κ : V → Observation d k → ℝ≥0∞) (g : V → Sphere d → ℝ≥0∞)
    (s : Sphere d) : ℝ≥0∞ :=
  ∫⁻ X : Rows d k, ∑ v, κ v (X,fun i => ⟪X i,s.val⟫)*g v s
    ∂Measure.pi (fun _ => stdGaussian (Vector d))

def terminalInput {d : ℕ} (π : Measure (Sphere d)) (ε : ℝ) (s : Sphere d) : ℝ≥0∞ :=
  π {u | Real.arccos ⟪u.val,s.val⟫ ≤ ε}

end SubsphereCurrent.Weighted
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe v
namespace SubsphereCurrent.Weighted

def RadiusWeightedFullEstimate : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ W : ℝ, 1 ≤ W → ∀ (V : Type v) [Fintype V] [Nonempty V],
      (Fintype.card V : ℝ) ≤ W →
      ∀ κ : V → Observation d (d/16) → ℝ≥0∞,
      (∀ v, Measurable (κ v)) → (∀ obs, ∑ v, κ v obs ≤ 1) →
      ∀ g : V → Sphere d → ℝ≥0∞,
      (∀ v, Measurable (g v)) → (∀ v s, g v s ≤ 1) →
      ∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      norm d n (blockInput κ g) ≤
        (ENNReal.ofReal W)^(1/((d/16 : ℕ) : ℝ))*ENNReal.ofReal (C^d)*(⨆ v, norm d (n-2) (g v))) ∧
    (∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      ∀ π : Measure (Sphere d), IsProbabilityMeasure π →
      ∀ ε : ℝ, 0 < ε →
      norm d n (terminalInput π ε) ≤ ENNReal.ofReal (C^d)*(ENNReal.ofReal ε)^((d : ℝ)/16))

end SubsphereCurrent.Weighted
end

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent

def HalfPrecision : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : SeededLearner d (M d) T Ω, L.Admissible ρ →
    (1/2 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.logb 2 (1/ε) ≤ (T : ℝ)
end SubsphereCurrent
end

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent
namespace Fixed

abbrev Vector (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Sphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

def sphereLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Sphere E) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

def rowsLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (T : ℕ) :
    Measure (Fin T → E) := Measure.pi fun _ => stdGaussian E

structure Stream (E J : Type*) [MeasurableSpace E] (T : ℕ) where
  initial : PMF J
  transition : ℕ → J → (E × ℝ) → PMF J
  output : J → Measure E
  output_probability : ∀ q, IsProbabilityMeasure (output q)

namespace Stream
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J]
  {T : ℕ}

def run (L : Stream E J T) (s : E) (x : Fin T → E) : ℕ → PMF J
  | 0 => L.initial
  | n+1 => (L.run s x n).bind fun q => if hn : n < T then
      L.transition (n+1) q (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s⟫)
    else PMF.pure q

def estimateLaw (L : Stream E J T) (s : E) (x : Fin T → E) : Measure E :=
  (L.run s x T).toMeasure.bind L.output

def euclideanSuccess (L : Stream E J T) (η : ℝ) (s : E) (x : Fin T → E) : ℝ≥0∞ :=
  L.estimateLaw s x {y | ‖y-s‖ ≤ η}

def angularSuccess (L : Stream E J T) (ε : ℝ) (s : E) (x : Fin T → E) : ℝ≥0∞ :=
  L.estimateLaw s x {y | Real.arccos ⟪y,s⟫ ≤ ε}

def BorelRules (L : Stream E J T) : Prop :=
  ∀ n q a, Measurable (fun obs => L.transition n q obs a)

def suffix (L : Stream E J T) (n k : ℕ) (v : J) : Stream E J k where
  initial := PMF.pure v
  transition t := L.transition (n+t)
  output := L.output
  output_probability := L.output_probability

end Stream

def DimensionEstimate : Prop :=
  ∃ C : ℝ, 2 ≤ C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ j m : ℕ,
    (d : ℝ)/2 + 2*j ≤ m → m ≤ d →
    ∀ η : ℝ, 0 < η →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → Stream (Vector m) (Fin (2^(d^2))) (j*(d/32)),
    (∀ᵐ ω ∂ρ, (L ω).BorelRules) →
    AEMeasurable (fun z : Sphere (Vector m) × (Ω × (Fin (j*(d/32)) → Vector m)) =>
      (L z.2.1).euclideanSuccess η z.1.val z.2.2)
      ((sphereLaw (Vector m)).prod (ρ.prod (rowsLaw (Vector m) (j*(d/32))))) →
    (∫⁻ z : Sphere (Vector m) × (Ω × (Fin (j*(d/32)) → Vector m)),
      (L z.2.1).euclideanSuccess η z.1.val z.2.2
        ∂(sphereLaw (Vector m)).prod (ρ.prod (rowsLaw (Vector m) (j*(d/32)))))
      ≤ ENNReal.ofReal ((C^(j+1)*η)^((d : ℝ)/32))

end Fixed
end SubsphereCurrent
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

def AllAffineFullEstimate : Prop :=
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ k : ℕ,
    (d+1)/2 + 2*k ≤ d → ∀ W : ℝ, 1 ≤ W →
    ∀ (J : Type v) [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J],
    (Fintype.card J : ℝ) ≤ W → W^(1/((d/8 : ℕ) : ℝ)) ≤ (2 : ℝ)^d →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → Fixed.Stream (Vector d) J (k*(d/16)),
    (∀ᵐ ω ∂ρ, (L ω).BorelRules ∧ ∀ q, ∀ᵐ y ∂(L ω).output q, ‖y‖ = 1) →
    ∀ ell : ℕ, ell ≤ k → ∀ v : J, ∀ n : ℕ, (d+1)/2 + 2*ell ≤ n →
    ∀ A : Test d n,
    (∫⁻ z : Sphere A.space × (Ω × (Fin (ell*(d/16)) → Vector d)),
      ((L z.2.1).suffix ((k-ell)*(d/16)) (ell*(d/16)) v).angularSuccess ε (A.point z.1) z.2.2
        ∂(sphereLaw A.space).prod (ρ.prod (Fixed.rowsLaw (Vector d) (ell*(d/16)))))
      ≤ ENNReal.ofReal (((16 * ((1000 : ℝ)^32)^ell * ε)/A.radius)^(2*(d/32)))

end SubsphereCurrent.Affine
end

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereRegression
section
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ
end
section
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def ambientSphereLaw : Measure E := (sphereLaw (E := E)).map Subtype.val
end
end SubsphereRegression
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Orthogonal (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :=
  unitary (E →L[ℝ] E)

instance orthogonal_compact : CompactSpace (Orthogonal E) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  rw [Metric.mem_closedBall,dist_zero_right]
  apply u.opNorm_le_bound (by norm_num)
  intro x
  simp only [u.norm_map_of_mem_unitary hu,one_mul,le_refl]

noncomputable def orthogonalLaw : Measure (Orthogonal E) :=
  Measure.haarMeasure ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
end SubsphereCurrent.Mixture
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def blockIso (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) : E ≃ₗᵢ[ℝ] E :=
  (V.orthogonalDecomposition.trans
    ((Unitary.linearIsometryEquiv u).withLpProdCongr 2 (Unitary.linearIsometryEquiv w))).trans
      V.orthogonalDecomposition.symm
end SubsphereCurrent.Mixture
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def directionLaw (V N : Submodule ℝ E) : Measure E :=
  ((orthogonalLaw (E := Vᗮ)).prod (SubsphereRegression.ambientSphereLaw (E := N))).map
    (fun z => blockIso V 1 z.1 (z.2 : E))

def directionJointLaw (V N : Submodule ℝ E) (t : ℕ) : Measure (Fin t → E) :=
  ((orthogonalLaw (E := Vᗮ)).prod
    (Measure.pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw (E := N)))).map
      (fun z i => blockIso V 1 z.1 (z.2 i : E))

def latitudeSpace (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) : Submodule ℝ E :=
  (ℝ ∙ (e.val : E))ᗮ

def latitudeLaw (V : Submodule ℝ E) (e : Metric.sphere (0 : V) 1) (a delta : ℝ) : Measure E :=
  ((betaMeasure a delta).prod ((orthogonalLaw (E := V)).prod
    (SubsphereRegression.ambientSphereLaw (E := latitudeSpace V e)))).map
      (fun z => blockIso V z.2.1 1
        (Real.sqrt (1-z.1) • (e.val : E) + Real.sqrt z.1 • (z.2.2 : E)))

def MixtureEstimate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Prop :=
  (∀ (V N : Submodule ℝ E), V ≤ N → 1 ≤ Module.finrank ℝ V →
    Module.finrank ℝ V < Module.finrank ℝ N → Module.finrank ℝ N < Module.finrank ℝ E →
    ∀ e : Metric.sphere (0 : V) 1,
    directionLaw V N ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E •
      (SubsphereRegression.ambientSphereLaw + latitudeLaw V e
        (((Module.finrank ℝ N : ℝ)-(Module.finrank ℝ V : ℝ))/2)
        (((Module.finrank ℝ E : ℝ)-(Module.finrank ℝ N : ℝ))/2))) ∧
  (∀ N : Submodule ℝ E, 1 ≤ Module.finrank ℝ N →
    directionLaw ⊥ N = SubsphereRegression.ambientSphereLaw) ∧
  (∀ (V : Submodule ℝ E) (t : ℕ), 1 ≤ Module.finrank ℝ E →
    directionJointLaw V ⊤ t =
      Measure.pi (fun _ : Fin t => SubsphereRegression.ambientSphereLaw))

end SubsphereCurrent.Mixture
end

noncomputable section
universe u v w
namespace SubsphereCurrent

def CurrentMainScope : Prop :=
  ExplicitPrecision.{u} ∧
  Weighted.RadiusWeightedFullEstimate.{v} ∧
  HalfPrecision.{u} ∧
  Affine.AllAffineFullEstimate.{u,v} ∧
  Fixed.DimensionEstimate.{u} ∧
  (∀ (E : Type w) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E], Mixture.MixtureEstimate E)

end SubsphereCurrent
end

noncomputable section
universe u v w
namespace SubsphereCurrent

def full_current_main_scope_statement : Prop :=
  CurrentMainScope.{u,v,w}

end SubsphereCurrent
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u, v, w} : Prop :=
  _root_.OAI.SubsphereCurrent.full_current_main_scope_statement.{u, v, w}

end Problem

/- Formalization scope, from lean/docs/140.md: In noiseless Gaussian regression, a learner observes inner products of an unknown unit vector in $\mathbb R^d$ with independent standard Gaussian vectors. The formalization proves that, for every fixed $A>0$, there is $c_A>0$ such that, in sufficiently large dimension, a learner retaining at most $Ad^2$ bits between observations needs at least $c_A d\log(1/\varepsilon)$ observations to attain angular error at most $\varepsilon$ with probability at least $2/3$ for a uniformly random unit signal, for $0<\varepsilon\le1/10$. For memory $o(d^2)$, the constant can be universal, and the selected statement also permits success at least $2/3$ separately for every signal. The linked supporting results include inverse Gram-matrix moments, exact-projection densities, regularization bounds, and sphere- and cube-prior block estimates. The paper studies how posterior replicas—independent signals drawn conditionally on the same observed data—control information in noiseless Gaussian regression. The formalization establishes the equal-label identity for finite measures, its density and measurable forms, and information bounds for Gaussian, distance, Haar, synthetic, and incidence comparisons. These statements retain exact observation labels, independent side randomness, and randomized transition rules. For a learner using $M(d)=o(d^2)$ bits of memory, the resulting bound says that, for sufficiently large $d$ and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform unit-sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations, where $c>0$ is universal. The formalized streaming result uses the $2/3$ threshold; the stronger $3/5$ variant is outside this scope. The formalization controls information gained from exact Gaussian observations of a spherical image of the uniform cube. Under the stated entropy and size conditions, repeated localization over $t$ observation blocks produces nested disclosures with mutual information at most $C(n+1)t$ and expected final localization level at most $Ct$. The selected estimates include inverse-volume control, kernel coercivity, and drift for the actual observation rows. For a law of finite relative entropy with respect to a uniform cell law in sufficiently large dimension, the regularization procedure terminates almost surely in regular cells. Its expected depth and number of attempts are finite, with at most twice one plus the expected depth in expectation; the remaining relative entropy plus $(\log 2)n/4$ times the expected depth is at most the initial relative entropy plus $2/e$. The paper uses projection moments and domination by positive spherical caps to bound the information carried by exact Gaussian observations of an unknown unit vector. The formalization covers integrated frame and sphere moments, cap domination, Riesz-density estimates with fixed offsets, and bounds valid at every radius. It also covers probability bounds for finite-memory learners at a fixed stopping time and after summing over stopping times. For $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations for a universal $c>0$. A corresponding bound holds when $M\le A d^2$ for each fixed $A>0$, with the constant allowed to depend on $A$. The randomized learner model allows independent shared seeds; its reduction to a finite-state model is proved for dimensions at least three, with the auxiliary dimension-two case outside this scope. The paper compares fresh Gaussian observations with observations coupled to information already held in memory. The formalization covers mixed-moment and actual-row estimates, critical-radius, one-level, and two-label comparisons, and conditional-information bounds across a block of observations. For sufficiently large dimension $d$, the relevant entropy bounds of order $d^2$ bound the information in the fresh experiment by that in the coupled experiment plus a term of order $d$; the associated block information increase also has order $d$. It also covers two-point identities on observation fibers and the fiber-block bound, including the boundary case of $d-2$ observed rows. The uniform unit-sphere prior, Gaussian rows, finite memory states, and randomized transition rules remain part of these statements. The separate streaming consequences and several intermediate comparison constructions are outside this selection. The paper uses subspheres to bound the number of exact Gaussian observations needed to estimate a unit vector with limited memory. The formalization proves that, for $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior, or for every unit signal, requires at least $2^{-16}d\log_2(1/\varepsilon)$ observations. Under the uniform prior, a lower bound of the same order with a universal positive constant holds at success probability $1/2$. The formalization also covers radius-weighted block and terminal estimates, affine and dimension estimates, and a vector-valued beta-mixture comparison with its boundary cases. These statements retain their dimension, width, radius, and suffix hypotheses, as well as the finite-state learner's independent randomness and restrictions on stopping and output. -/
