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

- problem_id: MemoryPrecision
- collection: openai-math
- question_id: openai-math:140
- source: openai-math
- source_locator: lean/ComparatorChallenges/MemoryPrecision.lean#OAI.MemoryPrecision.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For fixed A &gt; 0, a one-pass learner with $`Ad^2`$ persistent bits needs $`\Omega_A(d\log(1/\epsilon))`$ noiseless Gaussian samples to recover a unit vector to angular error $`0\lt \epsilon\le1/10`$ with probability 2/3, uniformly in accuracy for large d. Computation and randomized updates are unrestricted, but output uses only the terminal state, stopping index and fresh randomness. ([Lean](lean/docs/140.md)) For every fixed A &gt; 0, a learner that retains at most $`Ad^2`$ bits between fresh exact Gaussian linear measurements needs $`\Omega_A(d\log(1/\epsilon))`$ measurements to estimate a uniformly random unit vector to angular error at most ϵ, for any $`0\lt \epsilon\le 1/10`$, with probability at least 2/3. The constant is absolute for $`o(d^2)`$ memory. For a signal with density bounded by L relative to uniform probability on $`S^{d-1}`$, we bound the information in a finite message W formed from exact Gaussian measurements, conditional on an independent projection revealed only to the analyst. For explicit row counts proportional to d, the bound is $`O(H(W)/d+d+\log(2+\log L))`$. Consequently, a finite-state learner with $`o(d^2)`$ persistent bits and a deterministic sample horizon needs $`\Omega(d\log(1/\epsilon))`$ fresh noiseless Gaussian measurements for constant-probability angular accuracy $`0\lt \epsilon\le1/10`$ under the uniform spherical prior. For the image of a uniform cube under a spherical coordinate map, we prove that finite messages from t blocks of $`\Theta(d)`$ exact Gaussian measurements reveal only $`O_A(dt)`$ information when each message has at most $`\exp(Ad^2)`$ values, for fixed A. The same bound holds when each message is supplemented with a nested cell that restores the required geometric spread. We prove moment estimates for exact random projections of finite measures whose mass is controlled on Euclidean balls, and derive positive domination by countable sums of spherical cap measures. For learners with $`M=o(d^2)`$ bits of memory, these estimates give three proofs that uniform-sphere average success at least 2/3 at angular accuracy $`0\lt \epsilon\le1/10`$ requires $`\Omega(d\log(1/\epsilon))`$ noiseless Gaussian observations. The three proofs keep their different stopping and accuracy costs explicit. Replacing the Gaussian rows used to select a finite message by independent rows increases the remaining conditional information by at most $`Cd`$, for a uniform spherical signal, message entropy at most d2, and the specified row dimensions proportional to d. As an application, we prove that learners with $`M=o(d^2)`$ persistent bits need $`T=\Omega(d\log(1/\epsilon))`$ exact observations to attain uniform-sphere angular success at least 3/5, for $`0\lt \epsilon\le1/10`$ and a deterministic finite horizon. Let a finite-state streaming learner estimate a uniformly random unit vector from independent exact Gaussian linear measurements. We prove that $`o(d^2)`$ bits of persistent memory and angular success probability at least 2/3 require at least $`2^{-16}d\log_2(1/\epsilon)`$ samples for all sufficiently large d, uniformly for $`0\lt \epsilon\le1/10`$. The proof conditions each batch on its observed projection and controls the resulting random residual subsphere.
- notes: OpenAI math result family 140, Memory–sample lower bounds for noiseless Gaussian regression -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/140.md
- track: solved
- answer_shape: proof
- context_lemmas: space_finiteDimensional gaussianVariance_nonneg cube_second_coordinate_lt cube_coordinate_square_le sum_fin_split cubeCoords_first cubeCoords_second cubeCoords_tail cubeCoords_sum cubeEmbedding_norm cubePrior_dimension
- source_theorem: OAI.MemoryPrecision.main
- source_theorem_count: 1
- source_solution_module: OAI.Probability.MemoryPrecision.Main
- source_main_result: OAI.MemoryPrecision.main
- source_papers: preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf preprints/Projection-moments-positive-cap-domination-and-Riesz-estimates-on-the-sphere-September-27-2026/paper.pdf preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf preprints/Subsphere-methods-for-memory-sample-lower-bounds-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf
- source_scope_note: lean/docs/140.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

namespace MemoryPrecision.Kernel

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Sphere (d : ℕ) := Metric.sphere (0 : Vector d) 1

abbrev State (M : ℕ) := Fin (2^M)

abbrev Action (M : ℕ) := Bool × State M

abbrev Observations (d k : ℕ) := Fin k → (Vector d × ℝ)

abbrev Rows (d k : ℕ) := Fin k → Vector d

def UniformSphere (d : ℕ) : Measure (Sphere d) :=
  let euclideanGroup : NormedAddCommGroup (Vector d) :=
    PiLp.normedAddCommGroup
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
      (fun _ : Fin d => ℝ)
  let euclideanInner := PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)
  let σ := @Measure.toSphere (Vector d) euclideanGroup
    (@InnerProductSpace.toNormedSpace ℝ (Vector d) _
      euclideanGroup.toSeminormedAddCommGroup euclideanInner) inferInstance
    (@volume (Vector d) (@measureSpaceOfInnerProductSpace (Vector d)
      euclideanGroup euclideanInner inferInstance inferInstance inferInstance))
  (σ Set.univ)⁻¹ • σ

def RowLaw (d k : ℕ) : @Measure (Rows d k)
    (@MeasurableSpace.pi (Fin k) (fun _ => Vector d)
      (fun _ => @WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
        (Fin d → ℝ) inferInstance)) :=
  let euclideanMeasurable := @WithLp.measurableSpace
    (@OfNat.ofNat ℝ≥0∞ 2
      (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
    (Fin d → ℝ) inferInstance
  @Measure.pi (Fin k) (fun _ => Vector d) inferInstance (fun _ => euclideanMeasurable)
    (fun _ => @stdGaussian (Vector d)
    (PiLp.normedAddCommGroup
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
      (fun _ : Fin d => ℝ))
    (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)) inferInstance euclideanMeasurable)

def ObservationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

structure Policy (d M T : ℕ) where
  initial : Action M → ℝ≥0∞
  initial_sum : ∑ a, initial a = 1
  transition : ℕ → State M → (Vector d × ℝ) → Action M → ℝ≥0∞
  transition_sum : ∀ t j obs, ∑ a, transition t j obs a = 1
  output : ℕ → State M → Measure (Sphere d)
  output_probability : ∀ t j, IsProbabilityMeasure (output t j)

namespace Policy

def Completed {d M T : ℕ} (K : Policy d M T) : Prop :=
  ∀ t j a, AEMeasurable (fun obs => K.transition t j obs a) (ObservationReference d)

def eval {d M T : ℕ} {X : Type*} (K : Policy d M T)
    (w : ℕ → State M → X → ℝ≥0∞) (n : ℕ) :
    (k : ℕ) → State M → X → Observations d k → ℝ≥0∞
  | 0, j, s, _ => w n j s
  | k+1, j, s, obs => ∑ a : Action M, K.transition (n+1) j (obs 0) a *
      if a.1 then w (n+1) a.2 s else K.eval w (n+1) k a.2 s (Fin.tail obs)

def pathValue {d M T : ℕ} {X : Type*} (K : Policy d M T)
    (w : ℕ → State M → X → ℝ≥0∞) (s : X) (obs : Observations d T) : ℝ≥0∞ :=
  ∑ a : Action M, K.initial a * if a.1 then w 0 a.2 s else K.eval w 0 T a.2 s obs

def records {d T : ℕ} (s : Sphere d) (A : Rows d T) : Observations d T :=
  fun index => (A index, @inner ℝ (EuclideanSpace ℝ (Fin d))
    (@InnerProductSpace.toInner ℝ (EuclideanSpace ℝ (Fin d)) _
      (PiLp.seminormedAddCommGroup
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
        (fun _ : Fin d => ℝ))
      (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))) s.val (A index))

def outputTest {d M T : ℕ} (K : Policy d M T) (f : Sphere d × Sphere d → ℝ≥0∞)
    (t : ℕ) (j : State M) (s : Sphere d) : ℝ≥0∞ :=
  ∫⁻ v, f (s,v) ∂K.output t j

def angleTest {d : ℕ} (ε : ℝ)
    (point : MemoryPrecision.Kernel.Sphere d × MemoryPrecision.Kernel.Sphere d) : ℝ≥0∞ :=
  @ite ℝ≥0∞ (Real.arccos (@inner ℝ (EuclideanSpace ℝ (Fin d))
      (@InnerProductSpace.toInner ℝ (EuclideanSpace ℝ (Fin d)) _
        (PiLp.seminormedAddCommGroup
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
          (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      point.2.val point.1.val) ≤ ε) (Classical.propDecidable _) 1 0

def chordTest {d : ℕ} (ε : ℝ) (x : Sphere d × Sphere d) : ℝ≥0∞ :=
  {x : Sphere d × Sphere d | dist x.2.val x.1.val ≤ ε}.indicator (fun _ => 1) x

def experiment {d M T : ℕ} {Ω : Type u} (K : Ω → Policy d M T)
    (f : Sphere d × Sphere d → ℝ≥0∞) (z : Sphere d × (Ω × Rows d T)) : ℝ≥0∞ :=
  (K z.2.1).pathValue ((K z.2.1).outputTest f) z.1 (records z.1 z.2.2)

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (π : Measure (Sphere d)) : Prop where
  completed : ∀ᵐ ω ∂ρ, (K ω).Completed
  experiment : ∀ f : Sphere d × Sphere d → ℝ≥0∞, Measurable f →
    (∀ x, f x ≤ 1) → AEMeasurable (experiment K f) (π.prod (ρ.prod (RowLaw d T)))

def Success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (π : Measure (Sphere d)) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, experiment K (angleTest ε) z ∂π.prod (ρ.prod (RowLaw d T))

def ChordSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (π : Measure (Sphere d)) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, experiment K (chordTest ε) z ∂π.prod (ρ.prod (RowLaw d T))

end Policy
end MemoryPrecision.Kernel

namespace NoiselessRegression
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
end NoiselessRegression

namespace MemoryPrecision
open NoiselessRegression

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def J (β : ℝ) (m j : ℕ) : ℝ :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let three : ℝ := @OfNat.ofNat ℝ 3 (@instOfNatAtLeastTwo ℝ 3 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 1)))
  1 + three^j * two^β * (m : ℝ) / (β - (j : ℝ) - (m : ℝ))

def AmbientBallBound {d : ℕ} (μ : Measure (Space d)) (H β : ℝ) : Prop :=
  ∀ x : Space d, ∀ r : ℝ, 0 < r →
    μ (Metric.closedBall x r) ≤ ENNReal.ofReal (H * r^β)

def InverseGram {d p : ℕ} (m : ℕ) (v : Space d × (Fin (p-1) → Space d)) : ℝ≥0∞ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  letI : AddCommGroup (Space d) := WithLp.instAddCommGroup exponent (Fin d → ℝ)
  letI : Inner ℝ (Space d) := @InnerProductSpace.toInner ℝ (Space d) _
    (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
    (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
  ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ (fun i => v.2 i - v.1)).det)⁻¹ ^ m)

def MatrixLabelReference (d m : ℕ) : @Measure ((Fin m → Space d) × (Fin m → ℝ))
    (@MeasurableSpace.prod (Fin m → Space d) (Fin m → ℝ)
      (@MeasurableSpace.pi (Fin m) (fun _ => Space d)
        (fun _ => WithLp.measurableSpace
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
              (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
      inferInstance) :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanMeasurable := WithLp.measurableSpace exponent (Fin d → ℝ)
  let rowMeasurable := @MeasurableSpace.pi (Fin m) (fun _ => Space d)
    (fun _ => euclideanMeasurable)
  let rowLaw := @Measure.pi (Fin m) (fun _ => Space d) inferInstance
    (fun _ => euclideanMeasurable)
    (fun _ => @stdGaussian (Space d)
      (PiLp.normedAddCommGroup exponent (fun _ : Fin d => ℝ))
      (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
      inferInstance euclideanMeasurable)
  @Measure.prod _ _ rowMeasurable inferInstance rowLaw volume

def ProjectionLaw {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m : ℕ) : @Measure ((Fin m → Space d) × (Fin m → ℝ))
      (@MeasurableSpace.prod (Fin m → Space d) (Fin m → ℝ)
        (@MeasurableSpace.pi (Fin m) (fun _ => Space d)
          (fun _ => WithLp.measurableSpace
            (@OfNat.ofNat ℝ≥0∞ 2
              (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
                (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
        inferInstance) :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanMeasurable := WithLp.measurableSpace exponent (Fin d → ℝ)
  let rowMeasurable := @MeasurableSpace.pi (Fin m) (fun _ => Space d)
    (fun _ => euclideanMeasurable)
  let rowLaw := @Measure.pi (Fin m) (fun _ => Space d) inferInstance
    (fun _ => euclideanMeasurable)
    (fun _ => @stdGaussian (Space d)
      (PiLp.normedAddCommGroup exponent (fun _ : Fin d => ℝ))
      (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
      inferInstance euclideanMeasurable)
  @Measure.map ((Fin m → Space d) × Space d) ((Fin m → Space d) × (Fin m → ℝ))
    (@MeasurableSpace.prod _ _ rowMeasurable euclideanMeasurable)
    (@MeasurableSpace.prod _ _ rowMeasurable inferInstance)
    (fun pair => (pair.1, fun index => @inner ℝ (Space d)
      (@InnerProductSpace.toInner ℝ (Space d) _
        (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      pair.2 (pair.1 index)))
    (@Measure.prod _ _ rowMeasurable euclideanMeasurable rowLaw μ)

def ProjectedEllipsoid {d m : ℕ} (z : Space d) (R : ℝ) :
    Set ((Fin m → Space d) × (Fin m → ℝ)) :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanInner := @InnerProductSpace.toInner ℝ (Space d) _
    (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
    (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
  {pair | ∃ displacement ∈ @Metric.closedBall (Space d)
      (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.toLp exponent (fun _ => (0 : ℝ))) R,
    pair.2 = fun index => @inner ℝ (Space d) euclideanInner z (pair.1 index) +
      @inner ℝ (Space d) euclideanInner displacement (pair.1 index)}

def ProjectionNormScale (m p : ℕ) (H β R : ℝ) : ℝ :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  (two * Real.pi) ^ (-(m : ℝ) * ((p : ℝ)-1) / (two*(p : ℝ))) * H *
    R ^ (β - (m : ℝ)*(1-1/(p : ℝ))) *
    (∏ j ∈ Finset.range (p-1), J β m j) ^ (1/(p : ℝ))

def UniformSphere (d : ℕ) : @Measure (Space d)
    (WithLp.measurableSpace
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)) :=
  let euclideanMeasurable := WithLp.measurableSpace
    (@OfNat.ofNat ℝ≥0∞ 2
      (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
        (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)
  @Measure.map (Kernel.Sphere d) (Space d)
    (MeasurableSpace.comap Subtype.val euclideanMeasurable) euclideanMeasurable
    Subtype.val (Kernel.UniformSphere d)

def GaussianRegularization {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m : ℕ) (δ : ℝ)
    (Ay : (Fin m → Space d) × (Fin m → ℝ)) : ℝ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  ∫ signal, ∏ index, gaussianPDFReal 0 ⟨δ^2, sq_nonneg δ⟩
    (Ay.2 index - @inner ℝ (Space d)
      (@InnerProductSpace.toInner ℝ (Space d) _
        (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      signal (Ay.1 index)) ∂μ

def PointwiseDensity {d : ℕ} (μ : Measure (Space d)) (m : ℕ)
    (x : (Fin m → Space d) × (Fin m → ℝ)) : ℝ := by
  classical
  exact if h : ∃ l : ℝ, Tendsto (fun i : ℕ => GaussianRegularization μ m (1/(i:ℝ)) x)
      atTop (𝓝 l) then Classical.choose h else 0

lemma space_finiteDimensional (d : ℕ) : FiniteDimensional ℝ (Space d) := by
  infer_instance

def UnitBallVolume (m : ℕ) : ℝ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanGroup := PiLp.normedAddCommGroup exponent (fun _ : Fin m => ℝ)
  letI : MeasurableSpace (Space m) := WithLp.measurableSpace exponent (Fin m → ℝ)
  let euclideanVolume := @volume (Space m) (@measureSpaceOfInnerProductSpace (Space m)
    euclideanGroup (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin m => ℝ))
    (space_finiteDimensional m) inferInstance inferInstance)
  (euclideanVolume (@Metric.ball (Space m)
    (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin m => ℝ))
    (WithLp.toLp exponent (fun _ : Fin m => (0 : ℝ))) 1)).toReal

def CoordinateUnit (m : ℕ) : Space m :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  WithLp.toLp exponent (fun j : Fin m => if (j:ℕ) = 0 then (1:ℝ) else 0)

lemma gaussianVariance_nonneg (δ : ℝ) : 0 ≤ δ^2 := sq_nonneg δ

def GaussianKernel (m : ℕ) (δ : ℝ) (y : Space m) : ℝ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∏ index, gaussianPDFReal 0 ⟨δ^2, gaussianVariance_nonneg δ⟩
    (@WithLp.ofLp exponent (Fin m → ℝ) y index)

def RadialMixture (m : ℕ) (δ r : ℝ) : ℝ :=
  UnitBallVolume m * r^m * (r / δ^2) * GaussianKernel m δ (r • CoordinateUnit m)

abbrev Sphere (d : ℕ) := Metric.sphere (0 : Space d) 1

def SpherePrior (d : ℕ) : Measure (Sphere d) :=
  MemoryPrecision.Kernel.UniformSphere d

def SphereBallBound {d : ℕ} (h : Sphere d → ℝ≥0∞) (H α : ℝ) : Prop :=
  ∀ z : Space d, ∀ r : ℝ, 0 < r →
    (∫⁻ s in {s : Sphere d | dist s.val z ≤ r}, h s ∂SpherePrior d) ≤
      ENNReal.ofReal (H * r^α)

section WeightedImage
variable {X : Type*} [MeasurableSpace X] {d m N : ℕ}

def WeightedBlock (ι : X → Space d) (h : Fin N → X → ℝ≥0∞)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let euclideanMeasurable := @WithLp.measurableSpace exponent (Fin d → ℝ) inferInstance
  let rowMeasurable := @MeasurableSpace.pi (Fin m) (fun _ => Space d)
    (fun _ => euclideanMeasurable)
  @MeasureTheory.lintegral (Fin m → Space d) rowMeasurable
    (@Measure.pi (Fin m) (fun _ => Space d) inferInstance (fun _ => euclideanMeasurable)
      (fun _ => @stdGaussian (Space d)
        (PiLp.normedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))
        (space_finiteDimensional d) euclideanMeasurable))
    (fun rows => ∑ state, g state (rows, fun index => @inner ℝ (Space d)
      (@InnerProductSpace.toInner ℝ (Space d) _
        (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      (ι x) (rows index)) * h state x)

end WeightedImage

def SphereBlock {d m N : ℕ} (h : Fin N → Sphere d → ℝ≥0∞)
    (g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞)
    (s : Sphere d) : ℝ≥0∞ :=
  WeightedBlock Subtype.val h g s

abbrev CubeSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  fun (point : EuclideanSpace ℝ (Fin n)) => ∀ index : Fin n,
    @LE.le ℝ Real.instLE
      (@abs ℝ Real.lattice Real.instAddGroup
        (@WithLp.ofLp
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
              (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0))))
          (Fin n → ℝ) point index))
      (@HDiv.hDiv ℝ ℝ ℝ (@instHDiv ℝ Real.instDivInvMonoid.toDiv)
        (@OfNat.ofNat ℝ 1 (@One.toOfNat1 ℝ Real.instOne))
        (@OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))))

abbrev Cube (d : ℕ) := CubeSet (d/2)

def CubeLaw (d : ℕ) : Measure (Cube d) :=
  (volume : Measure (Space (d/2))).comap Subtype.val

lemma cube_second_coordinate_lt (d : ℕ) (index : Fin d)
    (lower : ¬index.val < d/2) (upper : index.val < 2*(d/2)) :
    index.val - d/2 < d/2 := by omega

def cubeRaw (d : ℕ) (u : Space (d/2)) : Space d :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  @HSMul.hSMul ℝ (Space d) (Space d)
    (@instHSMul ℝ (Space d) (WithLp.instSMul exponent ℝ (Fin d → ℝ)))
    (Real.sqrt (d/2:ℕ))⁻¹ (WithLp.toLp exponent (fun index : Fin d =>
      if lower : index.val < d/2 then
        @WithLp.ofLp exponent (Fin (d/2) → ℝ) u ⟨index.val, lower⟩
      else if upper : index.val < 2*(d/2) then
        Real.sqrt (1-(@WithLp.ofLp exponent (Fin (d/2) → ℝ) u
          ⟨index.val-d/2, cube_second_coordinate_lt d index lower upper⟩)^2)
      else 0))

def CubeEmbedding (d : ℕ) (u : Cube d) : Space d := cubeRaw d u.val

def CubeBall (d : ℕ) (z : Space (d/2)) (r : ℝ) : Set (Cube d) :=
  {u | dist u.val z ≤ Real.sqrt (d/2:ℕ) * r}

def CubeLocal {d : ℕ} (f : Cube d → ℝ≥0∞) (L : ℝ) : Prop :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let cubeMeasurable := @Subtype.instMeasurableSpace (Space (d/2)) (CubeSet (d/2))
    (@WithLp.measurableSpace exponent (Fin (d/2) → ℝ) inferInstance)
  ∀ z : Space (d/2), ∀ r : ℝ, 0 < r →
    @MeasureTheory.lintegral (Cube d) cubeMeasurable
      (@Measure.restrict (Cube d) cubeMeasurable (CubeLaw d) (CubeBall d z r)) f ≤
      ENNReal.ofReal (L * r^(
        (@OfNat.ofNat ℝ 3 (@instOfNatAtLeastTwo ℝ 3 Real.commRing.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 1)))) * (d/2:ℕ) /
        (@OfNat.ofNat ℝ 4 (@instOfNatAtLeastTwo ℝ 4 Real.commRing.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 2)))) : ℝ))

/-- Every coordinate of the paired cube has square at most one quarter. -/

lemma cube_coordinate_square_le {d : ℕ} (u : Cube d) (i : Fin (d/2)) : u.val i^2 ≤ 1/4 := by
  have hu : -(1/2 : ℝ) ≤ u.val i ∧ u.val i ≤ 1/2 := abs_le.mp (u.property i)
  nlinarith [sq_nonneg (u.val i-1/2), sq_nonneg (u.val i+1/2)]

lemma sum_fin_split {n d : ℕ} (hn : n ≤ d) (f : Fin d → ℝ) :
    (∑ i, f i) = (∑ i : Fin n, f ⟨i.val,by omega⟩) +
      ∑ i : Fin (d-n), f ⟨n+i.val,by omega⟩ := by
  let e : Fin (n+(d-n)) ≃ Fin d := finCongr (Nat.add_sub_of_le hn)
  calc
    _ = ∑ i : Fin (n+(d-n)), f (e i) := (Equiv.sum_comp e f).symm
    _ = _ := by rw [Fin.sum_univ_add]; rfl

def cubeCoords (d : ℕ) (u : Space (d/2)) : Space d :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  WithLp.toLp exponent (fun index : Fin d =>
    if lower : index.val < d/2 then
      @WithLp.ofLp exponent (Fin (d/2) → ℝ) u ⟨index.val, lower⟩
    else if upper : index.val < 2*(d/2) then
      Real.sqrt (1-(@WithLp.ofLp exponent (Fin (d/2) → ℝ) u
        ⟨index.val-d/2, cube_second_coordinate_lt d index lower upper⟩)^2)
    else 0)

lemma cubeCoords_first (d : ℕ) (u : Space (d/2)) (i : Fin (d/2)) :
    cubeCoords d u ⟨i.val,by omega⟩ = u i := by
  simp [cubeCoords, i.isLt]

lemma cubeCoords_second (d : ℕ) (u : Space (d/2)) (i : Fin (d/2)) :
    cubeCoords d u ⟨d/2+i.val,by omega⟩ = Real.sqrt (1-u i^2) := by
  simp [cubeCoords, show ¬d/2+i.val < d/2 by omega, show d/2+i.val < 2*(d/2) by omega]

lemma cubeCoords_tail (d : ℕ) (u : Space (d/2)) (i : Fin d) (hi : 2*(d/2) ≤ i.val) :
    cubeCoords d u i = 0 := by
  simp [cubeCoords, show ¬i.val < d/2 by omega, show ¬i.val < 2*(d/2) by omega]

lemma cubeCoords_sum (d : ℕ) (u : Space (d/2)) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ i : Fin d, f (cubeCoords d u i)) =
      (∑ i : Fin (d/2), f (u i)) + ∑ i : Fin (d/2), f (Real.sqrt (1-u i^2)) := by
  rw [sum_fin_split (show d/2 ≤ d by omega)]
  simp_rw [cubeCoords_first]
  rw [sum_fin_split (show d/2 ≤ d-d/2 by omega)]
  congr 1
  have h1 : (∑ i : Fin (d/2), f (cubeCoords d u ⟨d/2+i.val,by omega⟩)) =
      ∑ i : Fin (d/2), f (Real.sqrt (1-u i^2)) := by simp_rw [cubeCoords_second]
  rw [h1]
  have h0 : (∑ i : Fin (d-d/2-d/2), f (cubeCoords d u ⟨d/2+(d/2+i.val),by omega⟩)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [cubeCoords_tail d u _ (show 2*(d/2) ≤ d/2+(d/2+i.val) by omega), hf]
  rw [h0, add_zero]

lemma cubeEmbedding_norm {d : ℕ} (hd : 2 ≤ d) (u : Cube d) :
    @Norm.norm (Space d) (PiLp.instNorm
      (p := @OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (β := fun _ : Fin d => ℝ))
      (CubeEmbedding d u) = (1 : ℝ) := by
  have hs : ‖cubeCoords d u.val‖^2 = (d/2:ℕ) := by
    rw [EuclideanSpace.real_norm_sq_eq, cubeCoords_sum d u.val (fun x => x^2) (by norm_num)]
    have he (i : Fin (d/2)) : Real.sqrt (1-u.val i^2)^2 = 1-u.val i^2 :=
      Real.sq_sqrt (by have := cube_coordinate_square_le u i; linarith)
    simp_rw [he]
    rw [← Finset.sum_add_distrib]
    simp
  have hn : 0 < (d/2:ℕ) := by omega
  have hr : 0 < Real.sqrt (d/2:ℕ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnorm : ‖cubeCoords d u.val‖ = Real.sqrt (d/2:ℕ) := by
    rw [← Real.sqrt_sq (norm_nonneg _), hs]
  change ‖(Real.sqrt (d/2:ℕ))⁻¹ • cubeCoords d u.val‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hnorm, inv_mul_cancel₀ hr.ne']

def CubeSphere {d : ℕ} (hd : 2 ≤ d) (u : Cube d) : UnitSphere d :=
  ⟨CubeEmbedding d u, by simpa [Metric.mem_sphere, dist_zero_right] using cubeEmbedding_norm hd u⟩

def AmbientGramStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let three : ℝ := @OfNat.ofNat ℝ 3 (@instOfNatAtLeastTwo ℝ 3 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 1)))
  let four : ℝ := @OfNat.ofNat ℝ 4 (@instOfNatAtLeastTwo ℝ 4 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 2)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  (∀ (d m p : ℕ),
    letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
    letI : PseudoMetricSpace (Space d) :=
      PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)
    letI : AddCommGroup (Space d) := WithLp.instAddCommGroup exponent (Fin d → ℝ)
    letI : Module ℝ (Space d) := WithLp.instModule (p := exponent) (K := ℝ) (V := Fin d → ℝ)
    1 ≤ d → 1 ≤ m → 2 ≤ p →
    ∀ β R H : ℝ, (m : ℝ) + (p : ℝ) - two < β → 0 < R → 0 < H →
    ∀ (μ : Measure (Space d)), IsFiniteMeasure μ →
    ∀ z : Space d, μ.support ⊆ Metric.closedBall z R →
    AmbientBallBound μ H β →
    (∀ (j : ℕ), j ≤ p-2 → ∀ L : AffineSubspace ℝ (Space d),
      Nonempty L → Module.finrank ℝ L.direction = j →
      (∀ t : ℝ, 0 < t → t ≤ R →
        μ {s | Metric.infDist s L ≤ t} ≤
          ENNReal.ofReal (three^j * two^β * H * R^j * t^(β-(j:ℝ)))) ∧
      (∫⁻ s, (ENNReal.ofReal (Metric.infDist s L)) ^ (-(m:ℝ)) ∂μ) ≤
        ENNReal.ofReal (J β m j * H * R^(β-(m:ℝ)))) ∧
    (∀ᵐ v : Space d × (Fin (p-1) → Space d)
      ∂μ.prod (Measure.pi (fun _ : Fin (p-1) => μ)),
      LinearIndependent ℝ (fun i => v.2 i - v.1)) ∧
    (∫⁻ v : Space d × (Fin (p-1) → Space d), InverseGram m v
      ∂μ.prod (Measure.pi (fun _ : Fin (p-1) => μ))) ≤
      ENNReal.ofReal (H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) *
        ∏ j : Fin (p-1), J β m j)) ∧
  (∃ C : ℝ, 1 ≤ C ∧ ∀ (d m p : ℕ), 16 ≤ d → p = d/8 →
    1 ≤ m → m ≤ p → ∀ β : ℝ, ((d:ℝ)-1)/two ≤ β → β ≤ (d:ℝ)/two →
    (∀ j : ℕ, j ≤ p-2 →
      ((d:ℝ)-1)/two - two*(p:ℝ) + two ≤ β-(j:ℝ)-(m:ℝ) ∧
      (d:ℝ)/four + three/two ≤ ((d:ℝ)-1)/two - two*(p:ℝ) + two ∧
      J β m j ≤ C^d) ∧
    (∀ H R : ℝ, 0 < H → 0 < R →
      H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) * (∏ j : Fin (p-1), J β m j) ≤
        C^(d*(p-1)) * H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ))))

def FiniteDensityStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ,
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  1 ≤ d → 1 ≤ m → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d, ∀ μ : Measure (Space d), IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    ∃ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
      Measurable F ∧ (∀ x, 0 ≤ F x) ∧
      (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
        ProjectionLaw μ m ∧
      (∀ᵐ x ∂MatrixLabelReference d m, x ∉ ProjectedEllipsoid z R → F x = 0) ∧
      eLpNorm F (p : ℝ≥0∞) (MatrixLabelReference d m) ≤
        ENNReal.ofReal (ProjectionNormScale m p H β R)

def MeasurableTestStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ,
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  1 ≤ d → 1 ≤ m → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d, ∀ μ : Measure (Space d), IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    let ν := MatrixLabelReference d m
    let η := ProjectionLaw μ m
    let B := ENNReal.ofReal (ProjectionNormScale m p H β R)
    let α := 1-1/(p:ℝ)
    (∀ E, MeasurableSet E → ν E ≠ ∞ → η E ≤ B * (ν E)^α) ∧
    η ≪ ν ∧
    ∃ ηc : Measure (NullMeasurableSpace ((Fin m → Space d) × (Fin m → ℝ)) ν),
      (∀ E, NullMeasurableSet E ν → ηc E = η E) ∧
      (∀ E, NullMeasurableSet E ν → ν.completion E ≠ ∞ →
        ηc E ≤ B * (ν.completion E)^α) ∧
      (∀ φ : NullMeasurableSpace ((Fin m → Space d) × (Fin m → ℝ)) ν → ℝ≥0∞,
        Measurable φ → (∀ x, φ x ≤ 1) →
        (∫⁻ x, φ x ∂ηc) ≤ B * (∫⁻ x in ProjectedEllipsoid z R, φ x ∂ν.completion)^α)

def JointL1Statement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ,
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace exponent (Fin d → ℝ)
  2 ≤ d → 1 ≤ m → m < d → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d, ∀ μ : Measure (Space d), IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    μ ≪ UniformSphere d →
  ∀ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
    Measurable F → (∀ x, 0 ≤ F x) →
    (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m →
    Tendsto (fun δ => eLpNorm (fun Ay => GaussianRegularization μ m δ Ay - F Ay)
      1 (MatrixLabelReference d m)) (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧
    eLpNorm F (p : ℝ≥0∞) (MatrixLabelReference d m) ≤
      ENNReal.ofReal (ProjectionNormScale m p H β R)

def RadialMixtureRepresentation (m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    (∀ r : ℝ, 0 < r → 0 ≤ RadialMixture m δ r) ∧
    Measurable (RadialMixture m δ) ∧
    (∫ r in Set.Ioi 0, RadialMixture m δ r) = 1 ∧
    (∀ y : Space m, GaussianKernel m δ y =
      ∫ r in Set.Ioi ‖y‖, RadialMixture m δ r / (UnitBallVolume m * r^m))

def FullRankDensityFormula {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m : ℕ) : Prop :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ A : Fin m → Space d,
    @LinearIndependent (Fin m) ℝ (Space d) A Real.commRing.toSemiring
      (WithLp.instAddCommGroup exponent (Fin d → ℝ)).toAddCommMonoid
      (WithLp.instModule (p := exponent) (K := ℝ) (V := Fin d → ℝ)) →
    (volume : Measure (Fin m → ℝ)).withDensity
      (fun y => ENNReal.ofReal (PointwiseDensity μ m (A,y))) =
      @Measure.map (Space d) (Fin m → ℝ)
        (WithLp.measurableSpace exponent (Fin d → ℝ)) inferInstance
        (fun signal => fun index => @inner ℝ (Space d)
          (@InnerProductSpace.toInner ℝ (Space d) _
            (PiLp.seminormedAddCommGroup exponent (fun _ : Fin d => ℝ))
            (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
          signal (A index)) μ

def PointwiseDensityProperties {d : ℕ}
    (μ : @Measure (Space d)
      (WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
            (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)))
    (m p : ℕ) (H β R : ℝ) : Prop :=
  letI : MeasurableSpace (Space d) := WithLp.measurableSpace
    (@OfNat.ofNat ℝ≥0∞ 2
      (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
        (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (Fin d → ℝ)
  let reference : Measure ((Fin m → Space d) × (Fin m → ℝ)) := MatrixLabelReference d m
  RadialMixtureRepresentation m ∧
  (∀ x, 0 ≤ PointwiseDensity μ m x) ∧
  Measurable (PointwiseDensity μ m) ∧
  FullRankDensityFormula μ m ∧
  reference.withDensity (fun x => ENNReal.ofReal (PointwiseDensity μ m x)) =
    ProjectionLaw μ m ∧
  (∀ F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ,
    Measurable F → (∀ x, 0 ≤ F x) →
    reference.withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m → PointwiseDensity μ m =ᵐ[reference] F) ∧
  (∫⁻ x, ENNReal.ofReal (PointwiseDensity μ m x)^p ∂reference) ≤
    ENNReal.ofReal (ProjectionNormScale m p H β R)^p

def PointwiseDensityStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∀ d m p : ℕ, 2 ≤ d → 1 ≤ m → m < d → 2 ≤ p →
  ∀ β H R : ℝ, (m : ℝ)+(p : ℝ)-two < β → 0 < H → 0 < R →
  ∀ z : Space d,
  ∀ μ : @Measure (Space d) (WithLp.measurableSpace exponent (Fin d → ℝ)),
    IsFiniteMeasure μ →
    @Measure.support (Space d)
      (PiLp.topologicalSpace (p := exponent) (β := fun _ : Fin d => ℝ))
      (WithLp.measurableSpace exponent (Fin d → ℝ)) μ ⊆
      @Metric.closedBall (Space d)
        (PiLp.instPseudoMetricSpace (p := exponent) (β := fun _ : Fin d => ℝ)) z R →
    AmbientBallBound μ H β →
    μ ≪ UniformSphere d → PointwiseDensityProperties μ m p H β R

def CoefficientStepStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  ∃ C : ℝ, 1 ≤ C ∧ ∀ d m N : ℕ, 16 ≤ d →
    1 ≤ m → m ≤ d/8 → 1 ≤ N →
    ∀ α H : ℝ, ((d:ℝ)-1)/two ≤ α → α ≤ (d:ℝ)/two → 0 < H →
    ∀ h : Fin N → Sphere d → ℝ≥0∞,
      (∀ w, Measurable (h w)) → (∀ w s, h w s ≤ 1) →
      (∀ w, SphereBallBound (h w) H α) →
    ∀ g : Fin N → ((Fin m → Space d) × (Fin m → ℝ)) → ℝ≥0∞,
      (∀ w, Measurable (g w)) → (∀ x, ∑ w, g w x ≤ 1) →
      SphereBallBound (SphereBlock h g) (C^d * (N:ℝ)^(1/((d/8:ℕ):ℝ)) * H) α

def CubeBlockStatement : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ d k N : ℕ, 16 ≤ d → 1 ≤ k → k ≤ (d/2)/4 → 1 ≤ N →
    ∀ L : ℝ, 0 ≤ L → ∀ f : Fin N → Cube d → ℝ≥0∞,
      (∀ v, Measurable (f v)) → (∀ v u, f v u ≤ 1) → (∀ v, CubeLocal (f v) L) →
    ∀ g : Fin N → ((Fin k → Space d) × (Fin k → ℝ)) → ℝ≥0∞,
      (∀ v, Measurable (g v)) → (∀ x, ∑ v, g v x ≤ 1) →
      CubeLocal (WeightedBlock (CubeEmbedding d) f g)
        (C^(d/2) * (N:ℝ)^(1/(((d/2)/4:ℕ):ℝ)) * L)

end MemoryPrecision

namespace MemoryPrecision.Kernel
namespace Policy

def ModelAdmissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) : Prop :=
  ∀ π : Measure (Sphere d), IsProbabilityMeasure π → Admissible K ρ π

end Policy

open MemoryPrecision NoiselessRegression Policy

def CubePrior {d : ℕ} (hd : 2 ≤ d) : Measure (MemoryPrecision.Kernel.Sphere d) :=
  (CubeLaw d).map (CubeSphere hd)

def BlockCount (T p : ℕ) : ℕ := ⌈(T:ℝ)/(p:ℝ)⌉₊

def SourceEllipsoidStatement : Prop :=
  let two : ℝ := @OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let four : ℝ := @OfNat.ofNat ℝ 4 (@instOfNatAtLeastTwo ℝ 4 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 2)))
  let ten : ℝ := @OfNat.ofNat ℝ 10 (@instOfNatAtLeastTwo ℝ 10 Real.commRing.toNatCast
    (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 8)))
  ∃ C C₀ : ℝ, 1 ≤ C ∧ 1 ≤ C₀ ∧
  ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/ten →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ K : Ω → Policy d M T, Policy.Admissible K ρ (UniformSphere d) →
    Policy.Success K ρ (UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      (four^d * ε^(((d:ℝ)-1)/two) *
        (C^d * (((d/8+2)*2^M : ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^(BlockCount T (d/8)))) ∧
    Policy.ChordSuccess K ρ (UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      (C₀^d * ε^((d:ℝ)/two-1) *
        (C^d * (((2*(d/8)+4)*2^M : ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^(BlockCount T (d/8)))) ∧
    {x : Sphere d × Sphere d | Real.arccos (@inner ℝ (Vector d)
      (@InnerProductSpace.toInner ℝ (Vector d) _
        (PiLp.seminormedAddCommGroup
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
              (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0))))
          (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      x.2.val x.1.val) ≤ ε} ⊆
    {x | @Dist.dist (Vector d)
      (PiLp.instDist (p := @OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0))))
        (α := fun _ : Fin d => ℝ)) x.2.val x.1.val ≤ ε}

lemma cubePrior_dimension {d₀ d : ℕ} (hd₀ : 16 ≤ d₀) (hd : d₀ ≤ d) : 2 ≤ d :=
  Nat.le_trans (by decide : 2 ≤ 16) (Nat.le_trans hd₀ hd)

end MemoryPrecision.Kernel

namespace MemoryPrecision

def main_statement : Prop :=
  AmbientGramStatement ∧
  FiniteDensityStatement ∧
  MeasurableTestStatement ∧
  JointL1Statement ∧
  PointwiseDensityStatement ∧
  CoefficientStepStatement ∧
  Kernel.SourceEllipsoidStatement.{u} ∧
  CubeBlockStatement ∧
  (∃ D : ℝ, Real.exp 1 ≤ D ∧ ∃ d₀ : ℕ, ∃ hd₀ : 16 ≤ d₀, ∃ c : ℝ, 0 < c ∧
    ∀ d M T : ℕ, ∀ hd : d₀ ≤ d, M ≤ d^2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ K : Ω → MemoryPrecision.Kernel.Policy d M T,
      MemoryPrecision.Kernel.Policy.ModelAdmissible.{u} K ρ →
      MemoryPrecision.Kernel.Policy.Success K ρ
        (MemoryPrecision.Kernel.CubePrior (MemoryPrecision.Kernel.cubePrior_dimension hd₀ hd)) ε ≤
          min 1 (ENNReal.ofReal
            (D^((d/2)*(MemoryPrecision.Kernel.BlockCount T ((d/2)/4)+1)) * ε^((d/2:ℕ)/4:ℝ))) ∧
      ((∀ signal : MemoryPrecision.Kernel.Sphere d,
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) /
        (@OfNat.ofNat ℝ≥0∞ 3
          (@instOfNatAtLeastTwo ℝ≥0∞ 3 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) ≤
          (∫⁻ observation,
            MemoryPrecision.Kernel.Policy.experiment K
              (MemoryPrecision.Kernel.Policy.angleTest ε) (signal, observation)
            ∂ρ.prod (MemoryPrecision.Kernel.RowLaw d T))) →
        c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ))) ∧
  (∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 0 < d₀ ∧
    ∀ d M T : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → MemoryPrecision.Kernel.Policy d M T,
      MemoryPrecision.Kernel.Policy.Admissible L ρ (MemoryPrecision.Kernel.UniformSphere d) →
      MemoryPrecision.Kernel.Policy.Success L ρ (MemoryPrecision.Kernel.UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
        ((2*ε*Real.exp (C*(1+(M:ℝ)/(d:ℝ)^2)*(MemoryPrecision.Kernel.BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2))))

end MemoryPrecision

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.MemoryPrecision.main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/140.md: In noiseless Gaussian regression, a learner observes inner products of an unknown unit vector in $\mathbb R^d$ with independent standard Gaussian vectors. The formalization proves that, for every fixed $A>0$, there is $c_A>0$ such that, in sufficiently large dimension, a learner retaining at most $Ad^2$ bits between observations needs at least $c_A d\log(1/\varepsilon)$ observations to attain angular error at most $\varepsilon$ with probability at least $2/3$ for a uniformly random unit signal, for $0<\varepsilon\le1/10$. For memory $o(d^2)$, the constant can be universal, and the selected statement also permits success at least $2/3$ separately for every signal. The linked supporting results include inverse Gram-matrix moments, exact-projection densities, regularization bounds, and sphere- and cube-prior block estimates. The paper studies how posterior replicas—independent signals drawn conditionally on the same observed data—control information in noiseless Gaussian regression. The formalization establishes the equal-label identity for finite measures, its density and measurable forms, and information bounds for Gaussian, distance, Haar, synthetic, and incidence comparisons. These statements retain exact observation labels, independent side randomness, and randomized transition rules. For a learner using $M(d)=o(d^2)$ bits of memory, the resulting bound says that, for sufficiently large $d$ and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform unit-sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations, where $c>0$ is universal. The formalized streaming result uses the $2/3$ threshold; the stronger $3/5$ variant is outside this scope. The formalization controls information gained from exact Gaussian observations of a spherical image of the uniform cube. Under the stated entropy and size conditions, repeated localization over $t$ observation blocks produces nested disclosures with mutual information at most $C(n+1)t$ and expected final localization level at most $Ct$. The selected estimates include inverse-volume control, kernel coercivity, and drift for the actual observation rows. For a law of finite relative entropy with respect to a uniform cell law in sufficiently large dimension, the regularization procedure terminates almost surely in regular cells. Its expected depth and number of attempts are finite, with at most twice one plus the expected depth in expectation; the remaining relative entropy plus $(\log 2)n/4$ times the expected depth is at most the initial relative entropy plus $2/e$. The paper uses projection moments and domination by positive spherical caps to bound the information carried by exact Gaussian observations of an unknown unit vector. The formalization covers integrated frame and sphere moments, cap domination, Riesz-density estimates with fixed offsets, and bounds valid at every radius. It also covers probability bounds for finite-memory learners at a fixed stopping time and after summing over stopping times. For $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations for a universal $c>0$. A corresponding bound holds when $M\le A d^2$ for each fixed $A>0$, with the constant allowed to depend on $A$. The randomized learner model allows independent shared seeds; its reduction to a finite-state model is proved for dimensions at least three, with the auxiliary dimension-two case outside this scope. The paper compares fresh Gaussian observations with observations coupled to information already held in memory. The formalization covers mixed-moment and actual-row estimates, critical-radius, one-level, and two-label comparisons, and conditional-information bounds across a block of observations. For sufficiently large dimension $d$, the relevant entropy bounds of order $d^2$ bound the information in the fresh experiment by that in the coupled experiment plus a term of order $d$; the associated block information increase also has order $d$. It also covers two-point identities on observation fibers and the fiber-block bound, including the boundary case of $d-2$ observed rows. The uniform unit-sphere prior, Gaussian rows, finite memory states, and randomized transition rules remain part of these statements. The separate streaming consequences and several intermediate comparison constructions are outside this selection. The paper uses subspheres to bound the number of exact Gaussian observations needed to estimate a unit vector with limited memory. The formalization proves that, for $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior, or for every unit signal, requires at least $2^{-16}d\log_2(1/\varepsilon)$ observations. Under the uniform prior, a lower bound of the same order with a universal positive constant holds at success probability $1/2$. The formalization also covers radius-weighted block and terminal estimates, affine and dimension estimates, and a vector-valued beta-mixture comparison with its boundary cases. These statements retain their dimension, width, radius, and suffix hypotheses, as well as the finite-state learner's independent randomness and restrictions on stopping and output. -/
