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

- problem_id: GaussianReplacement
- collection: openai-math
- question_id: openai-math:140
- source: openai-math
- source_locator: lean/ComparatorChallenges/GaussianReplacement.lean#OAI.CurrentProjection.mixedMomentMain
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For fixed A &gt; 0, a one-pass learner with $`Ad^2`$ persistent bits needs $`\Omega_A(d\log(1/\epsilon))`$ noiseless Gaussian samples to recover a unit vector to angular error $`0\lt \epsilon\le1/10`$ with probability 2/3, uniformly in accuracy for large d. Computation and randomized updates are unrestricted, but output uses only the terminal state, stopping index and fresh randomness. ([Lean](lean/docs/140.md)) For every fixed A &gt; 0, a learner that retains at most $`Ad^2`$ bits between fresh exact Gaussian linear measurements needs $`\Omega_A(d\log(1/\epsilon))`$ measurements to estimate a uniformly random unit vector to angular error at most ϵ, for any $`0\lt \epsilon\le 1/10`$, with probability at least 2/3. The constant is absolute for $`o(d^2)`$ memory. For a signal with density bounded by L relative to uniform probability on $`S^{d-1}`$, we bound the information in a finite message W formed from exact Gaussian measurements, conditional on an independent projection revealed only to the analyst. For explicit row counts proportional to d, the bound is $`O(H(W)/d+d+\log(2+\log L))`$. Consequently, a finite-state learner with $`o(d^2)`$ persistent bits and a deterministic sample horizon needs $`\Omega(d\log(1/\epsilon))`$ fresh noiseless Gaussian measurements for constant-probability angular accuracy $`0\lt \epsilon\le1/10`$ under the uniform spherical prior. For the image of a uniform cube under a spherical coordinate map, we prove that finite messages from t blocks of $`\Theta(d)`$ exact Gaussian measurements reveal only $`O_A(dt)`$ information when each message has at most $`\exp(Ad^2)`$ values, for fixed A. The same bound holds when each message is supplemented with a nested cell that restores the required geometric spread. We prove moment estimates for exact random projections of finite measures whose mass is controlled on Euclidean balls, and derive positive domination by countable sums of spherical cap measures. For learners with $`M=o(d^2)`$ bits of memory, these estimates give three proofs that uniform-sphere average success at least 2/3 at angular accuracy $`0\lt \epsilon\le1/10`$ requires $`\Omega(d\log(1/\epsilon))`$ noiseless Gaussian observations. The three proofs keep their different stopping and accuracy costs explicit. Replacing the Gaussian rows used to select a finite message by independent rows increases the remaining conditional information by at most $`Cd`$, for a uniform spherical signal, message entropy at most d2, and the specified row dimensions proportional to d. As an application, we prove that learners with $`M=o(d^2)`$ persistent bits need $`T=\Omega(d\log(1/\epsilon))`$ exact observations to attain uniform-sphere angular success at least 3/5, for $`0\lt \epsilon\le1/10`$ and a deterministic finite horizon. Let a finite-state streaming learner estimate a uniformly random unit vector from independent exact Gaussian linear measurements. We prove that $`o(d^2)`$ bits of persistent memory and angular success probability at least 2/3 require at least $`2^{-16}d\log_2(1/\epsilon)`$ samples for all sufficiently large d, uniformly for $`0\lt \epsilon\le1/10`$. The proof conditions each batch on its observed projection and controls the resulting random residual subsphere.
- notes: OpenAI math result family 140, Memory–sample lower bounds for noiseless Gaussian regression -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/140.md
- track: solved
- answer_shape: proof
- context_lemmas: measurable_own_label measurable_blockInput sphere_standardBorel uniformSphere_probability_of_pos
- source_theorem: OAI.CurrentProjection.mixedMomentMain OAI.CurrentProjection.actualRowMain OAI.CurrentProjection.actualRowRefinement OAI.CurrentProjection.actualRowSourceMain OAI.CurrentProjection.actualRowSourceRefinement OAI.CurrentProjection.criticalComparisonMain OAI.CurrentProjection.oneLevelComparisonMain OAI.CurrentProjection.twoLabelComparisonMain OAI.CurrentProjection.hybridBlockMain OAI.CurrentProjection.fiberTwoPointMain OAI.CurrentProjection.fiberBlockMain
- source_theorem_count: 11
- source_solution_module: OAI.Probability.GaussianReplacement.FiberEquality
- source_main_result: OAI.CurrentProjection.fiberBlockMain
- source_papers: preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf preprints/Projection-moments-positive-cap-domination-and-Riesz-estimates-on-the-sphere-September-27-2026/paper.pdf preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf preprints/Subsphere-methods-for-memory-sample-lower-bounds-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf
- source_scope_note: lean/docs/140.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InformationTheory
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

namespace CurrentProjection

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Sphere (d : ℕ) := Metric.sphere (0 : Vector d) 1

abbrev Rows (k d : ℕ) := Fin k → Vector d

def uniformSphere (d : ℕ) : Measure (Sphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ

def gaussianRows (k d : ℕ) : Measure (Rows k d) :=
  Measure.pi fun _ => stdGaussian (Vector d)

def label {k d : ℕ} (g : Rows k d) (s : Vector d) : Fin k → ℝ :=
  fun i => ⟪s, g i⟫

def LocalGrowth {d : ℕ} (ρ : Measure (Sphere d)) (a : ℕ) (B : ℝ) : Prop :=
  ∀ z : Vector d, ∀ t : ℝ, 0 < t →
    ρ {u | dist (u : Vector d) z ≤ t} ≤ ENNReal.ofReal (B * t ^ a)

def cubeAverage {k d : ℕ} (ρ : Measure (Sphere d)) (g : Rows k d)
    (y : Fin k → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * δ)⁻¹ ^ k) *
    ρ {u | ∀ i, |label g (u : Vector d) i - y i| ≤ δ}

def exactDensity {k d : ℕ} (ρ : Measure (Sphere d)) (g : Rows k d)
    (y : Fin k → ℝ) : ℝ≥0∞ := by
  classical
  let f := fun j : ℕ => (cubeAverage ρ g y (1 / (j : ℝ))).toReal
  exact if h : ∃ L : ℝ, Tendsto f atTop (𝓝 L) then ENNReal.ofReal h.choose else 0

def AdmissibleDimensions (d m r q : ℕ) : Prop :=
  1 ≤ m ∧ 1 ≤ r ∧ 1 ≤ q ∧ m + r < d - 1 ∧ m + r - m - (q - 1) ≥ 1

def momentConstant (C : ℝ) (d : ℕ) (B D : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (C * d) * B * (1 + max (Real.log (D / B)) 0))

def MixedMomentMain : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d m r q : ℕ), AdmissibleDimensions d m r q →
    ∀ (ρ : Measure (Sphere d)), IsFiniteMeasure ρ →
    ∀ (B D : ℝ), 0 < B → 0 < D → LocalGrowth ρ (m+r) B → LocalGrowth ρ (d-1) D →
    (∀ (s : Sphere d) (δ : ℝ), 0 < δ →
      (∫⁻ X, (∫⁻ Z, cubeAverage ρ (Fin.append X Z)
        (label (Fin.append X Z) (s : Vector d)) δ ∂gaussianRows r d)^q
          ∂gaussianRows m d) ≤ (momentConstant C d B D)^q) ∧
    (ρ ≪ uniformSphere d → ∃ E : Set (Sphere d), MeasurableSet E ∧ ρ E = 0 ∧
      ∀ s ∉ E,
        (∀ᵐ G ∂gaussianRows (m+r) d,
          Tendsto (fun δ : ℝ => cubeAverage ρ G (label G (s : Vector d)) δ)
            (𝓝[>] 0) (𝓝 (exactDensity ρ G (label G (s : Vector d))))) ∧
        ((∫⁻ X, (∫⁻ Z, exactDensity ρ (Fin.append X Z)
          (label (Fin.append X Z) (s : Vector d)) ∂gaussianRows r d)^q
            ∂gaussianRows m d) ≤ (momentConstant C d B D)^q) ∧
        (ρ ≠ 0 → ∀ᵐ G ∂gaussianRows (m+r) d,
          0 < exactDensity ρ G (label G (s : Vector d)) ∧
          exactDensity ρ G (label G (s : Vector d)) < ∞))

instance gaussianRows_isProbabilityMeasure (k d : ℕ) : IsProbabilityMeasure (gaussianRows k d) := by
  unfold gaussianRows
  infer_instance

lemma measurable_own_label {k d : ℕ} :
    Measurable (fun z : Rows k d × Sphere d => label z.1 (z.2:Vector d)) := by
  apply Measurable.of_eval
  intro i
  exact (continuous_inner.comp <| (continuous_subtype_val.comp continuous_snd).prodMk
    ((continuous_apply i).comp continuous_fst)).measurable

def swapLast {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] :
    (A × B) × C ≃ᵐ (A × C) × B where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  measurable_invFun := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

def rowInformation {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] (P : Measure ((S×W)×X)) (γ : Measure X) : ℝ≥0∞ :=
  klDiv P (P.fst.prod γ)

noncomputable def shannonEntropy {W : Type*} [MeasurableSpace W] (π : Measure W) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (-Real.log (π {w}).toReal) ∂π

def conditionalMutualInformation {Z A B : Type*} [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure (Z×(A×B))) [IsFiniteMeasure P] : ℝ≥0∞ := by
  classical
  exact if h : Nonempty (A×B) then
    letI := h
    InformationTheory.klDiv P (P.fst ⊗ₘ (P.condKernel.fst ×ₖ P.condKernel.snd))
  else 0

def actualExperiment {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d × W) × Rows m d)) :
    Measure (((Sphere d × W) × Rows m d) × Rows r d) := P.prod (gaussianRows r d)

instance actualExperiment_isProbabilityMeasure {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (actualExperiment (r:=r) P) :=
  inferInstanceAs (IsProbabilityMeasure (P.prod (gaussianRows r d)))

def actualObservation {d m r : ℕ} {W : Type*}
    (p : ((Sphere d × W) × Rows m d) × Rows r d) :
    (Rows (m+r) d × W) × (Fin (m+r) → ℝ) :=
  ((Fin.append p.1.2 p.2,p.1.1.2), label (Fin.append p.1.2 p.2) (p.1.1.1 : Vector d))

instance actualObservation_isProbabilityMeasure {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure ((actualExperiment (r:=r) P).map actualObservation) :=
  inferInstance

def selectedCube {k d : ℕ} {W : Type*} (ρ : W → Measure (Sphere d)) (δ : ℝ)
    (z : (Rows k d×W)×(Fin k → ℝ)) : ℝ≥0∞ := cubeAverage (ρ z.1.2) z.1.1 z.2 δ

def selectedExact {k d : ℕ} {W : Type*} (ρ : W → Measure (Sphere d))
    (z : (Rows k d×W)×(Fin k → ℝ)) : ℝ≥0∞ := exactDensity (ρ z.1.2) z.1.1 z.2

def momentBound (C : ℝ) (d : ℕ) (B D : ℝ) : ℝ :=
  Real.exp (C*d)*B*(1+max (Real.log (D/B)) 0)

def logPositive (x : ℝ≥0∞) : ℝ := max (Real.log x.toReal) 0

def logNegative (x : ℝ≥0∞) : ℝ≥0∞ := if x = 0 then ∞ else ENNReal.ofReal (-Real.log x.toReal)

def extendedLogExpectation {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ≥0∞) : EReal :=
  ((∫⁻ a, ENNReal.ofReal (logPositive (f a)) ∂μ) : EReal) -
    ((∫⁻ a, logNegative (f a) ∂μ) : EReal)

def PositiveMessage {W : Type*} [MeasurableSpace W] (π : Measure W) := {w : W // 0 < π {w}}

def completeFamily {W : Type*} [MeasurableSpace W] {T : Type*} (π : Measure W)
    (f : PositiveMessage π → T) (t₀ : T) (w : W) : T :=
  if h : 0 < π {w} then f ⟨w,h⟩ else t₀

structure ActualRowConclusion {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ρ : W → Measure (Sphere d)) (B D : W → ℝ) : Prop where
  row_finite : rowInformation P (gaussianRows m d) ≠ ∞
  row_le_entropy : (rowInformation P (gaussianRows m d)).toReal ≤
    (shannonEntropy (P.map swapLast).snd).toReal
  conditional_density : ∀ᵐ gw ∂((actualExperiment (r:=r) P).map actualObservation).fst,
    ((actualExperiment (r:=r) P).map actualObservation).condKernel gw ≪ volume
  actual_limit : ∀ᵐ p ∂actualExperiment (r:=r) P,
    Tendsto (fun j : ℕ => selectedCube ρ (1/(j:ℝ)) (actualObservation p)) atTop
      (𝓝 (selectedExact ρ (actualObservation p)))
  smoothed_bound : ∀ δ : ℝ, 0 < δ →
    Integrable (fun p => Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal))
      (actualExperiment (r:=r) P) ∧
    (∫ p, Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
      (rowInformation P (gaussianRows m d)).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  exact_integrable : Integrable (fun p => Real.log (1+(selectedExact ρ (actualObservation p)).toReal))
    (actualExperiment (r:=r) P)
  exact_bound : (∫ p, Real.log (1+(selectedExact ρ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
    (rowInformation P (gaussianRows m d)).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  entropy_bound : (rowInformation P (gaussianRows m d)).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst ≤
    (shannonEntropy (P.map swapLast).snd).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  positive_log_integrable : Integrable (fun p => logPositive (selectedExact ρ (actualObservation p)))
    (actualExperiment (r:=r) P)
  extended_log_bound : extendedLogExpectation (actualExperiment (r:=r) P)
    (fun p => selectedExact ρ (actualObservation p)) ≤
      (((rowInformation P (gaussianRows m d)).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst) : EReal)

def actualConditionalRowInformation {d m : ℕ} {W : Type*} [MeasurableSpace W]
    [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsFiniteMeasure P] : ℝ≥0∞ :=
  conditionalMutualInformation (P.map (fun p => (p.1.1,(p.2,p.1.2))))

structure ActualRowSourceConclusion {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ρ : W → Measure (Sphere d)) (B D : W → ℝ) : Prop where
  row_finite : actualConditionalRowInformation P ≠ ∞
  row_le_entropy : (actualConditionalRowInformation P).toReal ≤
    (shannonEntropy (P.map swapLast).snd).toReal
  conditional_density : ∀ᵐ gw ∂((actualExperiment (r:=r) P).map actualObservation).fst,
    ((actualExperiment (r:=r) P).map actualObservation).condKernel gw ≪ volume
  actual_limit : ∀ᵐ p ∂actualExperiment (r:=r) P,
    Tendsto (fun j : ℕ => selectedCube ρ (1/(j:ℝ)) (actualObservation p)) atTop
      (𝓝 (selectedExact ρ (actualObservation p)))
  smoothed_bound : ∀ δ : ℝ, 0 < δ →
    Integrable (fun p => Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal))
      (actualExperiment (r:=r) P) ∧
    (∫ p, Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
      (actualConditionalRowInformation P).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  exact_integrable : Integrable (fun p => Real.log (1+(selectedExact ρ (actualObservation p)).toReal))
    (actualExperiment (r:=r) P)
  exact_bound : (∫ p, Real.log (1+(selectedExact ρ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
    (actualConditionalRowInformation P).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  entropy_bound : (actualConditionalRowInformation P).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst ≤
    (shannonEntropy (P.map swapLast).snd).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  positive_log_integrable : Integrable (fun p => logPositive (selectedExact ρ (actualObservation p)))
    (actualExperiment (r:=r) P)
  extended_log_bound : extendedLogExpectation (actualExperiment (r:=r) P)
    (fun p => selectedExact ρ (actualObservation p)) ≤
      (((actualConditionalRowInformation P).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst) : EReal)

def alignedExperiment {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) : Measure ((Sphere d×W)×Rows (m+r) d) :=
  (actualExperiment (r:=r) P).map (fun p => (p.1.1,Fin.append p.1.2 p.2))

instance alignedExperiment_probability {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (alignedExperiment (r:=r) P) := by
  unfold alignedExperiment
  infer_instance

def exposedJointMap {d k : ℕ} {W : Type*} (p : (Sphere d×W)×Rows k d) :
    (Rows k d×(Fin k → ℝ))×(Sphere d×W) := ((p.2,label p.2 (p.1.1:Vector d)),p.1)

def exposedInformation {d k : ℕ} {W : Type*} [MeasurableSpace W] [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsFiniteMeasure P] : ℝ≥0∞ :=
  conditionalMutualInformation (P.map exposedJointMap)

def CriticalComparisonMain : Prop :=
  ∃ (K : ℝ) (d₀ : ℕ), 0 < K ∧ ∀ (d : ℕ), d₀ ≤ d →
    ∀ (W : Type) [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W],
    ∀ (P : Measure ((Sphere d×W)×Rows (d/10) d)) [IsProbabilityMeasure P],
    (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/10) d) →
    shannonEntropy (P.map swapLast).snd ≤ ENNReal.ofReal ((d:ℝ)^2) →
    exposedInformation (P.fst.prod (gaussianRows (d/10+(d/2-d/10)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/2-d/10) P) + ENNReal.ofReal (K*d)

def OneLevelComparisonMain : Prop :=
  ∃ (C : ℝ) (d₀ : ℕ), 0 < C ∧ ∀ d, d₀ ≤ d →
    ∀ (U : Type) [MeasurableSpace U] [Finite U] [MeasurableSingletonClass U],
    ∀ (P : Measure ((Sphere d×U)×Rows (d/32) d)) [IsProbabilityMeasure P],
    (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/32) d) →
    exposedInformation (P.fst.prod (gaussianRows (d/32+(d/4-d/32)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/4-d/32) P) +
      ENNReal.ofReal (C*((d:ℝ)+Real.log (1+(d:ℝ)+(shannonEntropy P.fst.snd).toReal)+
        (shannonEntropy P.fst.snd).toReal/(d:ℝ)))

def TwoLabelComparisonMain : Prop :=
  ∃ (C : ℝ) (d₀ : ℕ), 0 < C ∧ ∀ d, d₀ ≤ d →
    ∀ (V : Type) [MeasurableSpace V] [Finite V] [MeasurableSingletonClass V],
    ∀ (P : Measure ((Sphere d×V)×Rows (d/8) d)) [IsProbabilityMeasure P],
    (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/8) d) →
    shannonEntropy P.fst.snd ≤ ENNReal.ofReal ((d:ℝ)^2) →
    exposedInformation (P.fst.prod (gaussianRows (d/8+(d/2-d/8)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/2-d/8) P) + ENNReal.ofReal (C*d)

def blockInput {d m : ℕ} {U : Type*} (z : (Sphere d × U) × Rows m d) :
    U × (Rows m d × (Fin m → ℝ)) :=
  (z.1.2, z.2, label z.2 (z.1.1 : Vector d))

lemma measurable_blockInput {d m : ℕ} {U : Type*} [MeasurableSpace U] :
    Measurable (blockInput (d:=d) (m:=m) (U:=U)) := by
  exact measurable_fst.snd.prodMk (measurable_snd.prodMk
    ((measurable_own_label (d:=d) (k:=m)).comp
      (measurable_snd.prodMk measurable_fst.fst)))

def blockLaw {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U))
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) :
    Measure (((Sphere d × U) × Rows m d) × V) :=
  (P.prod (gaussianRows m d)) ⊗ₘ κ.comap blockInput measurable_blockInput

instance blockLaw_probability {d m : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U)) [IsProbabilityMeasure P]
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) [IsMarkovKernel κ] :
    IsProbabilityMeasure (blockLaw P κ) := by
  unfold blockLaw
  infer_instance

def endingSignalLaw {d m : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U))
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) : Measure (Sphere d × V) :=
  (blockLaw P κ).map (fun z => (z.1.1.1, z.2))

instance endingSignalLaw_probability {d m : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U)) [IsProbabilityMeasure P]
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) [IsMarkovKernel κ] :
    IsProbabilityMeasure (endingSignalLaw P κ) := by
  unfold endingSignalLaw
  infer_instance

def freshInformation {d : ℕ} {U : Type*} [MeasurableSpace U] [StandardBorelSpace U]
    (P : Measure (Sphere d × U)) [IsFiniteMeasure P] (k : ℕ) : ℝ≥0∞ :=
  exposedInformation (P.prod (gaussianRows k d))

def hybridFirst (d : ℕ) : ℕ := (d+3)/4

def hybridLast (d : ℕ) : ℕ := d/2

def hybridCount (d : ℕ) : ℕ := hybridLast d - hybridFirst d + 1

def averagedFreshInformation {d : ℕ} {U : Type*}
    [MeasurableSpace U] [StandardBorelSpace U]
    (P : Measure (Sphere d × U)) [IsFiniteMeasure P] : ℝ :=
  (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d), (freshInformation P k).toReal) /
    hybridCount d

def HybridBlockMain : Prop :=
  ∃ (C C' : ℝ) (d₀ : ℕ), 0 < C ∧ 0 < C' ∧ ∀ d, d₀ ≤ d →
    ∀ m, 1 ≤ m → m ≤ d/8 →
    ∀ (U V : Type) [Fintype U] [Fintype V]
      [MeasurableSpace U] [MeasurableSpace V]
      [MeasurableSingletonClass U] [MeasurableSingletonClass V],
    ∀ (P : Measure (Sphere d × U)) [IsProbabilityMeasure P],
    P.fst = uniformSphere d →
    ∀ (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) [IsMarkovKernel κ],
    ∀ (B : ℝ), 0 ≤ B →
    shannonEntropy (endingSignalLaw P κ).snd ≤ ENNReal.ofReal B →
    averagedFreshInformation (endingSignalLaw P κ) - averagedFreshInformation P ≤
      C*m + (m:ℝ) / hybridCount d * (C + B / (d/8:ℕ)) + B / (d/32:ℕ) ∧
    (B ≤ (d:ℝ)^2 →
      averagedFreshInformation (endingSignalLaw P κ) - averagedFreshInformation P ≤ C'*d)

def FiberBlockMain : Prop :=
  ∃ (K : ℝ) (d₀ : ℕ), 0 < K ∧ ∀ d, d₀ ≤ d →
    ∀ (U V : Type) [Fintype U] [Fintype V]
      [MeasurableSpace U] [MeasurableSpace V]
      [MeasurableSingletonClass U] [MeasurableSingletonClass V],
    ∀ (P : Measure (Sphere d×U)) [IsProbabilityMeasure P],
    P.fst = uniformSphere d →
    ∀ (κ : Kernel (U×(Rows (d/10) d×(Fin (d/10)→ℝ))) V) [IsMarkovKernel κ],
    ∀ N : ℕ, 1 ≤ N → Fintype.card V ≤ N → Real.log N ≤ (d:ℝ)^2 →
    freshInformation (endingSignalLaw P κ) (d/3) ≤ freshInformation P (d/3) + ENNReal.ofReal (K*d)

def dependentMapKernel {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) (f : A×B → D) : Kernel A D :=
  (Kernel.id ×ₖ κ).map f

def fiberObservationLaw (d k : ℕ) : Measure ((Rows k d×(Fin k→ℝ))×Sphere d) :=
  ((gaussianRows k d).prod (uniformSphere d)).map
    (fun z => ((z.1,label z.1 (z.2:Vector d)),z.2))

instance uniformSphere_finite (d : ℕ) : IsFiniteMeasure (uniformSphere d) := by
  constructor
  unfold uniformSphere
  rw [Measure.smul_apply, smul_eq_mul]
  exact lt_of_le_of_lt (ENNReal.inv_mul_le_one _) ENNReal.one_lt_top

instance fiberObservationLaw_finite (d k : ℕ) : IsFiniteMeasure (fiberObservationLaw d k) := by
  unfold fiberObservationLaw
  infer_instance

lemma sphere_standardBorel (d : ℕ) : StandardBorelSpace (Sphere d) :=
  Metric.isClosed_sphere.measurableSet.standardBorel

def sphericalFiberKernel (d k : ℕ) [sphereNonempty : Nonempty (Sphere d)] :
    Kernel (Rows k d×(Fin k→ℝ)) (Sphere d) :=
  @Measure.condKernel (Rows k d×(Fin k→ℝ)) (Sphere d) _ _
    (sphere_standardBorel d) sphereNonempty
    (fiberObservationLaw d k) (fiberObservationLaw_finite d k)

instance sphericalFiberKernel_markov (d k : ℕ) [Nonempty (Sphere d)] :
    IsMarkovKernel (sphericalFiberKernel d k) := by
  unfold sphericalFiberKernel
  infer_instance

def fiberTwoPointLeft (d k : ℕ) [Nonempty (Sphere d)] : Measure (Rows k d×(Sphere d×Sphere d)) :=
  ((((gaussianRows k d).prod (uniformSphere d)).withDensity
    (fun z => exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d)))) ⊗ₘ
    ((sphericalFiberKernel d k).comap (fun z => (z.1,label z.1 (z.2:Vector d)))
      (measurable_fst.prodMk measurable_own_label))).map
    (fun z => (z.1.1,(z.1.2,z.2)))

def perpendicularRow {d : ℕ} (v g : Vector d) : Vector d :=
  letI : NormedAddCommGroup (Vector d) := PiLp.normedAddCommGroup 2 (fun _ : Fin d => ℝ)
  letI : InnerProductSpace ℝ (Vector d) := PiLp.innerProductSpace (fun _ : Fin d => ℝ)
  g - (⟪v,g⟫ / ‖v‖^2) • v

def perpendicularRowsKernel (d k : ℕ) : Kernel (Sphere d×Sphere d) (Rows k d) :=
  dependentMapKernel (Kernel.const (Sphere d×Sphere d) (gaussianRows k d))
    (fun z => fun i => perpendicularRow ((z.1.1:Vector d)-(z.1.2:Vector d)) (z.2 i))

def fiberTwoPointConstant (k : ℕ) : ℝ≥0∞ :=
  letI : OfNat ℝ 2 := @instOfNatAtLeastTwo ℝ 2 Real.instNatCast inferInstance
  letI : Mul ℝ := Real.instMul
  letI : Inv ℝ := Real.instInv
  letI : Pow ℝ ℕ := @NPow.toPow ℝ Real.instMonoid.toNPow
  ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹ ^ k)

def fiberDistanceWeight {d : ℕ} (k : ℕ) (z : Sphere d×Sphere d) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖(z.1:Vector d)-(z.2:Vector d)‖)⁻¹ ^ k

def fiberTwoPointRight (d k : ℕ) : Measure (Rows k d×(Sphere d×Sphere d)) :=
  letI : IsScalarTower ℝ≥0∞ ℝ≥0∞ ℝ≥0∞ := Semigroup.isScalarTower
  fiberTwoPointConstant k •
    Measure.map (Prod.swap : (Sphere d×Sphere d)×Rows k d → Rows k d×(Sphere d×Sphere d))
      (Measure.compProd
        (Measure.withDensity (Measure.prod (uniformSphere d) (uniformSphere d))
          (fiberDistanceWeight k))
        (perpendicularRowsKernel d k))

lemma uniformSphere_probability_of_pos {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (uniformSphere d) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  constructor
  rw [uniformSphere, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero
    (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := Vector d)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'


def FiberTwoPointMain : Prop :=
  ∀ (d k : ℕ) (_hk : 1 ≤ k) (hkd : k < d-1),
    letI : IsProbabilityMeasure (uniformSphere d) :=
      uniformSphere_probability_of_pos (by omega)
    letI : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
    IsFiniteMeasure (fiberTwoPointLeft d k) ∧ IsFiniteMeasure (fiberTwoPointRight d k) ∧
      fiberTwoPointLeft d k = fiberTwoPointRight d k

def mixedMomentMain_statement : Prop :=
  MixedMomentMain

def actualRowMain_statement : Prop :=
  ∀ {d m r q : ℕ} {W : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W] (hdim : AdmissibleDimensions d m r q) (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (ν : Measure (Sphere d)) [IsProbabilityMeasure ν] (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d) (hEntropy : shannonEntropy (P.map swapLast).snd ≠ ∞) (ρ : PositiveMessage (P.map swapLast).snd → Measure (Sphere d)) [∀ w, IsFiniteMeasure (ρ w)] (_hρac : ∀ w, ρ w ≪ uniformSphere d) (B D : PositiveMessage (P.map swapLast).snd → ℝ) (hB : ∀ w, 0 < B w) (hD : ∀ w, 0 < D w) (hgB : ∀ w, LocalGrowth (ρ w) (m+r) (B w)) (hgD : ∀ w, LocalGrowth (ρ w) (d-1) (D w)) (hCI : Integrable (fun sw : Sphere d×W => Real.log (1+momentBound 9 d
      (completeFamily (P.map swapLast).snd B 1 sw.2) (completeFamily (P.map swapLast).snd D 1 sw.2))) P.fst),
    ActualRowConclusion (r:=r) (q:=q) P (completeFamily (P.map swapLast).snd ρ 0)
      (completeFamily (P.map swapLast).snd B 1) (completeFamily (P.map swapLast).snd D 1)

def actualRowRefinement_statement : Prop :=
  ∀ {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W] [Countable E] [MeasurableSingletonClass E] (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (e : Sphere d×W → E) (he : Measurable e) (_hEntropy : shannonEntropy
      ((P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))).map swapLast).snd ≠ ∞),
    rowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) (gaussianRows m d) =
      rowInformation P (gaussianRows m d)

def actualRowSourceMain_statement : Prop :=
  ∀ {d m r q : ℕ} {W : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W] (hdim : AdmissibleDimensions d m r q) (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (ν : Measure (Sphere d)) [IsProbabilityMeasure ν] (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d) (hEntropy : shannonEntropy (P.map swapLast).snd ≠ ∞) (ρ : PositiveMessage (P.map swapLast).snd → Measure (Sphere d)) [∀ w, IsFiniteMeasure (ρ w)] (_hρac : ∀ w, ρ w ≪ uniformSphere d) (B D : PositiveMessage (P.map swapLast).snd → ℝ) (hB : ∀ w, 0 < B w) (hD : ∀ w, 0 < D w) (hgB : ∀ w, LocalGrowth (ρ w) (m+r) (B w)) (hgD : ∀ w, LocalGrowth (ρ w) (d-1) (D w)) (hCI : Integrable (fun sw : Sphere d×W => Real.log (1+momentBound 9 d
      (completeFamily (P.map swapLast).snd B 1 sw.2) (completeFamily (P.map swapLast).snd D 1 sw.2))) P.fst),
    ActualRowSourceConclusion (r:=r) (q:=q) P (completeFamily (P.map swapLast).snd ρ 0)
      (completeFamily (P.map swapLast).snd B 1) (completeFamily (P.map swapLast).snd D 1)

def actualRowSourceRefinement_statement : Prop :=
  ∀ {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W] [Countable E] [MeasurableSingletonClass E] (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] (ν : Measure (Sphere d)) [IsProbabilityMeasure ν] (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d)) (e : Sphere d×W → E) (he : Measurable e) (hEntropy : shannonEntropy
      ((P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))).map swapLast).snd ≠ ∞),
    actualConditionalRowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) =
      actualConditionalRowInformation P

def criticalComparisonMain_statement : Prop :=
  CriticalComparisonMain

def oneLevelComparisonMain_statement : Prop :=
  OneLevelComparisonMain

def twoLabelComparisonMain_statement : Prop :=
  TwoLabelComparisonMain

def hybridBlockMain_statement : Prop :=
  HybridBlockMain

def fiberTwoPointMain_statement : Prop :=
  FiberTwoPointMain

def fiberBlockMain_statement : Prop :=
  FiberBlockMain

end CurrentProjection

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1, u_2} : Prop :=
  _root_.OAI.CurrentProjection.mixedMomentMain_statement ∧
  _root_.OAI.CurrentProjection.actualRowMain_statement.{u_1} ∧
  _root_.OAI.CurrentProjection.actualRowRefinement_statement.{u_1, u_2} ∧
  _root_.OAI.CurrentProjection.actualRowSourceMain_statement.{u_1} ∧
  _root_.OAI.CurrentProjection.actualRowSourceRefinement_statement.{u_1, u_2} ∧
  _root_.OAI.CurrentProjection.criticalComparisonMain_statement ∧
  _root_.OAI.CurrentProjection.oneLevelComparisonMain_statement ∧
  _root_.OAI.CurrentProjection.twoLabelComparisonMain_statement ∧
  _root_.OAI.CurrentProjection.hybridBlockMain_statement ∧
  _root_.OAI.CurrentProjection.fiberTwoPointMain_statement ∧
  _root_.OAI.CurrentProjection.fiberBlockMain_statement

end Problem

/- Formalization scope, from lean/docs/140.md: In noiseless Gaussian regression, a learner observes inner products of an unknown unit vector in $\mathbb R^d$ with independent standard Gaussian vectors. The formalization proves that, for every fixed $A>0$, there is $c_A>0$ such that, in sufficiently large dimension, a learner retaining at most $Ad^2$ bits between observations needs at least $c_A d\log(1/\varepsilon)$ observations to attain angular error at most $\varepsilon$ with probability at least $2/3$ for a uniformly random unit signal, for $0<\varepsilon\le1/10$. For memory $o(d^2)$, the constant can be universal, and the selected statement also permits success at least $2/3$ separately for every signal. The linked supporting results include inverse Gram-matrix moments, exact-projection densities, regularization bounds, and sphere- and cube-prior block estimates. The paper studies how posterior replicas—independent signals drawn conditionally on the same observed data—control information in noiseless Gaussian regression. The formalization establishes the equal-label identity for finite measures, its density and measurable forms, and information bounds for Gaussian, distance, Haar, synthetic, and incidence comparisons. These statements retain exact observation labels, independent side randomness, and randomized transition rules. For a learner using $M(d)=o(d^2)$ bits of memory, the resulting bound says that, for sufficiently large $d$ and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform unit-sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations, where $c>0$ is universal. The formalized streaming result uses the $2/3$ threshold; the stronger $3/5$ variant is outside this scope. The formalization controls information gained from exact Gaussian observations of a spherical image of the uniform cube. Under the stated entropy and size conditions, repeated localization over $t$ observation blocks produces nested disclosures with mutual information at most $C(n+1)t$ and expected final localization level at most $Ct$. The selected estimates include inverse-volume control, kernel coercivity, and drift for the actual observation rows. For a law of finite relative entropy with respect to a uniform cell law in sufficiently large dimension, the regularization procedure terminates almost surely in regular cells. Its expected depth and number of attempts are finite, with at most twice one plus the expected depth in expectation; the remaining relative entropy plus $(\log 2)n/4$ times the expected depth is at most the initial relative entropy plus $2/e$. The paper uses projection moments and domination by positive spherical caps to bound the information carried by exact Gaussian observations of an unknown unit vector. The formalization covers integrated frame and sphere moments, cap domination, Riesz-density estimates with fixed offsets, and bounds valid at every radius. It also covers probability bounds for finite-memory learners at a fixed stopping time and after summing over stopping times. For $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations for a universal $c>0$. A corresponding bound holds when $M\le A d^2$ for each fixed $A>0$, with the constant allowed to depend on $A$. The randomized learner model allows independent shared seeds; its reduction to a finite-state model is proved for dimensions at least three, with the auxiliary dimension-two case outside this scope. The paper compares fresh Gaussian observations with observations coupled to information already held in memory. The formalization covers mixed-moment and actual-row estimates, critical-radius, one-level, and two-label comparisons, and conditional-information bounds across a block of observations. For sufficiently large dimension $d$, the relevant entropy bounds of order $d^2$ bound the information in the fresh experiment by that in the coupled experiment plus a term of order $d$; the associated block information increase also has order $d$. It also covers two-point identities on observation fibers and the fiber-block bound, including the boundary case of $d-2$ observed rows. The uniform unit-sphere prior, Gaussian rows, finite memory states, and randomized transition rules remain part of these statements. The separate streaming consequences and several intermediate comparison constructions are outside this selection. The paper uses subspheres to bound the number of exact Gaussian observations needed to estimate a unit vector with limited memory. The formalization proves that, for $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior, or for every unit signal, requires at least $2^{-16}d\log_2(1/\varepsilon)$ observations. Under the uniform prior, a lower bound of the same order with a universal positive constant holds at success probability $1/2$. The formalization also covers radius-weighted block and terminal estimates, affine and dimension estimates, and a vector-valued beta-mixture comparison with its boundary cases. These statements retain their dimension, width, radius, and suffix hypotheses, as well as the finite-state learner's independent randomness and restrictions on stopping and output. -/
