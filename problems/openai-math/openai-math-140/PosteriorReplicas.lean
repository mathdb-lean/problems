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

- problem_id: PosteriorReplicas
- collection: openai-math
- question_id: openai-math:140
- source: openai-math
- source_locator: lean/ComparatorChallenges/PosteriorReplicas.lean#OAI.PosteriorReplicas.source_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For fixed A &gt; 0, a one-pass learner with $`Ad^2`$ persistent bits needs $`\Omega_A(d\log(1/\epsilon))`$ noiseless Gaussian samples to recover a unit vector to angular error $`0\lt \epsilon\le1/10`$ with probability 2/3, uniformly in accuracy for large d. Computation and randomized updates are unrestricted, but output uses only the terminal state, stopping index and fresh randomness. ([Lean](lean/docs/140.md)) For every fixed A &gt; 0, a learner that retains at most $`Ad^2`$ bits between fresh exact Gaussian linear measurements needs $`\Omega_A(d\log(1/\epsilon))`$ measurements to estimate a uniformly random unit vector to angular error at most ϵ, for any $`0\lt \epsilon\le 1/10`$, with probability at least 2/3. The constant is absolute for $`o(d^2)`$ memory. For a signal with density bounded by L relative to uniform probability on $`S^{d-1}`$, we bound the information in a finite message W formed from exact Gaussian measurements, conditional on an independent projection revealed only to the analyst. For explicit row counts proportional to d, the bound is $`O(H(W)/d+d+\log(2+\log L))`$. Consequently, a finite-state learner with $`o(d^2)`$ persistent bits and a deterministic sample horizon needs $`\Omega(d\log(1/\epsilon))`$ fresh noiseless Gaussian measurements for constant-probability angular accuracy $`0\lt \epsilon\le1/10`$ under the uniform spherical prior. For the image of a uniform cube under a spherical coordinate map, we prove that finite messages from t blocks of $`\Theta(d)`$ exact Gaussian measurements reveal only $`O_A(dt)`$ information when each message has at most $`\exp(Ad^2)`$ values, for fixed A. The same bound holds when each message is supplemented with a nested cell that restores the required geometric spread. We prove moment estimates for exact random projections of finite measures whose mass is controlled on Euclidean balls, and derive positive domination by countable sums of spherical cap measures. For learners with $`M=o(d^2)`$ bits of memory, these estimates give three proofs that uniform-sphere average success at least 2/3 at angular accuracy $`0\lt \epsilon\le1/10`$ requires $`\Omega(d\log(1/\epsilon))`$ noiseless Gaussian observations. The three proofs keep their different stopping and accuracy costs explicit. Replacing the Gaussian rows used to select a finite message by independent rows increases the remaining conditional information by at most $`Cd`$, for a uniform spherical signal, message entropy at most d2, and the specified row dimensions proportional to d. As an application, we prove that learners with $`M=o(d^2)`$ persistent bits need $`T=\Omega(d\log(1/\epsilon))`$ exact observations to attain uniform-sphere angular success at least 3/5, for $`0\lt \epsilon\le1/10`$ and a deterministic finite horizon. Let a finite-state streaming learner estimate a uniformly random unit vector from independent exact Gaussian linear measurements. We prove that $`o(d^2)`$ bits of persistent memory and angular success probability at least 2/3 require at least $`2^{-16}d\log_2(1/\epsilon)`$ samples for all sufficiently large d, uniformly for $`0\lt \epsilon\le1/10`$. The proof conditions each batch on its observed projection and controls the resulting random residual subsphere.
- notes: OpenAI math result family 140, Memory–sample lower bounds for noiseless Gaussian regression -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/140.md
- track: solved
- answer_shape: proof
- context_lemmas: measurable_labels
- source_theorem: OAI.PosteriorReplicas.source_main
- source_theorem_count: 1
- source_solution_module: OAI.Probability.PosteriorReplicas.Main
- source_main_result: OAI.PosteriorReplicas.source_main
- source_papers: preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf preprints/Projection-moments-positive-cap-domination-and-Riesz-estimates-on-the-sphere-September-27-2026/paper.pdf preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf preprints/Subsphere-methods-for-memory-sample-lower-bounds-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf
- source_scope_note: lean/docs/140.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix
open scoped ENNReal NNReal RealInnerProductSpace Classical

noncomputable section

namespace PosteriorReplicas

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Rows (d k : ℕ) := Fin k → Vec d
abbrev Labels (k : ℕ) := Fin k → ℝ
abbrev Data (d k : ℕ) := Rows d k × Labels k
abbrev Tuple (d m : ℕ) := Fin (m + 1) → Vec d

def sphereLaw (d : ℕ) : Measure (Vec d) :=
  let σ := (volume : Measure (Vec d)).toSphere
  ((σ univ)⁻¹ • σ).map Subtype.val

def gaussianRows (d k : ℕ) : Measure (Rows d k) :=
  Measure.pi fun _ => stdGaussian (Vec d)

instance (d k : ℕ) : IsProbabilityMeasure (gaussianRows d k) := by
  unfold gaussianRows
  infer_instance

def labels {d k : ℕ} (A : Rows d k) (s : Vec d) : Labels k :=
  fun i => ⟪A i, s⟫

lemma measurable_labels {d k : ℕ} :
    Measurable (fun z : Rows d k × Vec d => labels z.1 z.2) := by
  unfold labels
  fun_prop

def messageKernel {d k N : ℕ} (κ : Kernel (Data d k) (Fin N)) :
    Kernel (Vec d × Rows d k) (Fin N) :=
  κ.comap (fun z => (z.2, labels z.2 z.1)) (by
    unfold labels
    fun_prop)

instance {d k N : ℕ} (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    IsMarkovKernel (messageKernel κ) := by
  unfold messageKernel
  infer_instance

def signalMessageLaw {d k N : ℕ} (p : Measure (Vec d))
    (κ : Kernel (Data d k) (Fin N)) : Measure (Vec d × Fin N) :=
  ((p.prod (gaussianRows d k)) ⊗ₘ messageKernel κ).map
    (fun z => (z.1.1, z.2))

instance {d k N : ℕ} (p : Measure (Vec d)) [IsProbabilityMeasure p]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    IsProbabilityMeasure (signalMessageLaw p κ) := by
  unfold signalMessageLaw
  infer_instance

def sideLaw {d N : ℕ} (ℓ : ℕ) (q : Measure (Vec d × Fin N)) :
    Measure (Data d ℓ × (Vec d × Fin N)) :=
  ((gaussianRows d ℓ).prod q).map
    (fun z => ((z.1, labels z.1 z.2.1), z.2))

instance {d N : ℕ} (ℓ : ℕ) (q : Measure (Vec d × Fin N)) [IsProbabilityMeasure q] :
    IsProbabilityMeasure (sideLaw ℓ q) := by
  unfold sideLaw
  infer_instance

def messageEntropy {d N : ℕ} (q : Measure (Vec d × Fin N)) : ℝ :=
  ∑ w : Fin N, -(q.snd.real {w}) * Real.log (q.snd.real {w})

def conditionalInformation {d ℓ N : ℕ} [NeZero N]
    (μ : Measure (Data d ℓ × (Vec d × Fin N))) [IsFiniteMeasure μ] : ℝ≥0∞ :=
  klDiv μ (μ.fst ⊗ₘ (μ.condKernel.fst ×ₖ μ.condKernel.snd))

def GaussianReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    let k := 2 * (d / 16)
    let t := k + 1
    let ℓ := 4 * k
    ∀ (p : Measure (Vec d)) [IsProbabilityMeasure p]
      (f : Vec d → ℝ) (L : ℝ),
      Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ L) →
      p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ (N : ℕ) [NeZero N] (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ],
        conditionalInformation (sideLaw ℓ (signalMessageLaw p κ)) ≤
          ENNReal.ofReal (messageEntropy (signalMessageLaw p κ) / (t : ℝ) +
            C * (d : ℝ) + C * Real.log (2 + Real.log L))

inductive BaseLaw where
  | spherical
  | gaussian
  deriving DecidableEq

def BaseLaw.measure (base : BaseLaw) (d : ℕ) : Measure (Vec d) :=
  match base with
  | .spherical => sphereLaw d
  | .gaussian => stdGaussian (Vec d)

def rowGram {d k : ℕ} (A : Rows d k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ⟪A i, A j⟫

def liftLabel {d k : ℕ} (A : Rows d k) (y : Labels k) : Vec d :=
  ∑ i, ((rowGram A)⁻¹ *ᵥ y) i • A i

def kernelComponent {d k : ℕ} (A : Rows d k) (x : Vec d) : Vec d :=
  x - liftLabel A (labels A x)

def baseFiber {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    Measure (Vec d) :=
  match base with
  | .gaussian => (stdGaussian (Vec d)).map
      (fun x => liftLabel A y + kernelComponent A x)
  | .spherical => (stdGaussian (Vec d)).map
      (fun x => liftLabel A y +
        (Real.sqrt (1 - ‖liftLabel A y‖ ^ 2) / ‖kernelComponent A x‖) •
          kernelComponent A x)

def baseDensity {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  if LinearIndependent ℝ A then
    match base with
    | .gaussian => ENNReal.ofReal
        ((2 * Real.pi) ^ (-(k : ℝ) / 2) *
          Real.exp (-‖liftLabel A y‖ ^ 2 / 2) / Real.sqrt (rowGram A).det)
    | .spherical => if ‖liftLabel A y‖ < 1 then ENNReal.ofReal
        (Real.Gamma ((d : ℝ) / 2) /
          (Real.pi ^ ((k : ℝ) / 2) * Real.Gamma (((d : ℝ) - k) / 2)) *
          (1 - ‖liftLabel A y‖ ^ 2) ^ (((d : ℝ) - k - 2) / 2) /
          Real.sqrt (rowGram A).det) else 0
  else 0

def tiltMass {d k : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  ∫⁻ x, f x ∂baseFiber base A y

def projectedDensity {d k : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  baseDensity base A y * tiltMass base f A y

def tiltedFiber {d k : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (A : Rows d k) (y : Labels k) : Measure (Vec d) :=
  if tiltMass base f A y = 0 then Measure.dirac 0
  else (tiltMass base f A y)⁻¹ • (baseFiber base A y).withDensity f

def differences {d m : ℕ} (u : Tuple d m) : Fin m → Vec d :=
  fun i => u i.succ - u 0

def differenceSpan {d m : ℕ} (u : Tuple d m) : Submodule ℝ (Vec d) :=
  Submodule.span ℝ (Set.range (differences u))

def affineVolume {d m : ℕ} (u : Tuple d m) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (differences u)).det

def constrainedRows {d m : ℕ} (k : ℕ) (u : Tuple d m) : Measure (Rows d k) :=
  (gaussianRows d k).map
    (fun A i => (differenceSpan u)ᗮ.starProjection (A i))

def equalLabelLeft {d k m : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (H : Rows d k × Labels k × Tuple d m → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ A, ∫⁻ y, (projectedDensity base f A y) ^ (m + 1) *
    ∫⁻ u, H (A, y, u) ∂Measure.pi (fun _ : Fin (m + 1) => tiltedFiber base f A y)
      ∂volume ∂gaussianRows d k

def equalLabelRight {d k m : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (H : Rows d k × Labels k × Tuple d m → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(k * m : ℝ) / 2)) *
    ∫⁻ u, (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
      ∫⁻ A, H (A, labels A (u 0), u) ∂constrainedRows k u
      ∂Measure.pi (fun _ : Fin (m + 1) => (base.measure d).withDensity f)

def EqualLabelMeasureIdentity : Prop :=
  ∀ (d k m : ℕ), 1 ≤ k → 1 ≤ m → k + m ≤ d - 2 →
    ∀ (base : BaseLaw) (f : Vec d → ℝ≥0∞), Measurable f →
      (∃ L : ℝ≥0∞, L ≠ ∞ ∧ ∀ x, f x ≤ L) →
      equalLabelLeft (k := k) (m := m) base f (fun _ => 1) < ∞ ∧
      ∀ H : Rows d k × Labels k × Tuple d m → ℝ≥0∞,
        Measurable H → equalLabelLeft base f H = equalLabelRight base f H

def DistanceReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (p : Measure (Vec d)) [IsProbabilityMeasure p]
      (f : Vec d → ℝ) (b : ℝ),
      0 ≤ b → Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp b) →
      p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ (N : ℕ) [NeZero N] (κ : Kernel (Data d (d / 16)) (Fin N)) [IsMarkovKernel κ],
        conditionalInformation (sideLaw (d / 2) (signalMessageLaw p κ)) ≤
          ENNReal.ofReal (messageEntropy (signalMessageLaw p κ) / ((d / 8 : ℕ) : ℝ) +
            C * ((d : ℝ) + b / (d : ℝ)))

def SyntheticReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 16 ≤ d →
    ∀ (p : Measure (Vec d)) [IsProbabilityMeasure p]
      (f : Vec d → ℝ) (L : ℝ),
      1 ≤ L → Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ L) →
      p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ (N : ℕ) [NeZero N] (z : Data d (d / 8) → Fin N) (hz : Measurable z),
        conditionalInformation
          (sideLaw (d / 2) (signalMessageLaw p (Kernel.deterministic z hz))) ≤
          ENNReal.ofReal (Real.log (N : ℝ) / ((d / 8 : ℕ) : ℝ) +
            C * ((d : ℝ) + Real.log (1 + Real.log L)))

def IncidenceReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (p : Measure (Vec d)) [IsProbabilityMeasure p]
      (f : Vec d → ℝ) (F : ℝ),
      1 ≤ F → Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ F) →
      p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ (N : ℕ) [NeZero N] (κ : Kernel (Data d (d / 16)) (Fin N)) [IsMarkovKernel κ],
        conditionalInformation (sideLaw (d / 4) (signalMessageLaw p κ)) ≤
          ENNReal.ofReal (Real.log (N : ℝ) / ((d / 16 : ℕ) : ℝ) +
            C * (d : ℝ) + C * Real.log (1 + Real.log F))

def labelNorm {k : ℕ} (y : Labels k) : ℝ := ‖WithLp.toLp 2 y‖

def ballDensityVersion {d k : ℕ} (ν : Measure (Vec d))
    (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ =>
    ((volume : Measure (Labels k)) {v | labelNorm v < (n + 1 : ℝ)⁻¹})⁻¹ *
      ν {x | labelNorm (labels A x - y) < (n + 1 : ℝ)⁻¹}) Filter.atTop

def gaussianDensityVersion {d k : ℕ} (ν : Measure (Vec d))
    (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ => ∫⁻ x,
    ENNReal.ofReal ((2 * Real.pi * ((n + 1 : ℝ)⁻¹)^2) ^ (-(k : ℝ) / 2) *
      Real.exp (-(labelNorm (labels A x - y))^2 / (2 * ((n + 1 : ℝ)⁻¹)^2))) ∂ν)
    Filter.atTop

def EqualLabelVersions : Prop :=
  ∀ (d k m : ℕ), 1 ≤ k → 1 ≤ m → k + m ≤ d - 2 →
    ∀ (base : BaseLaw) (f : Vec d → ℝ≥0∞), Measurable f →
      (∃ L : ℝ≥0∞, L ≠ ∞ ∧ ∀ x, f x ≤ L) →
      let ν := (base.measure d).withDensity f
      (Measurable (fun z : Rows d k × Labels k => projectedDensity base f z.1 z.2)) ∧
      (Measurable (fun z : Rows d k × Labels k => ballDensityVersion ν z.1 z.2)) ∧
      (Measurable (fun z : Rows d k × Labels k => gaussianDensityVersion ν z.1 z.2)) ∧
      (∀ A : Rows d k, LinearIndependent ℝ A →
        ν.map (labels A) = volume.withDensity (projectedDensity base f A) ∧
        projectedDensity base f A =ᵐ[volume] ballDensityVersion ν A ∧
        projectedDensity base f A =ᵐ[volume] gaussianDensityVersion ν A) ∧
      (∀ᵐ u ∂Measure.pi (fun _ : Fin (m + 1) => ν),
        LinearIndependent ℝ (differences u) ∧
        ∀ᵐ A ∂constrainedRows k u,
          LinearIndependent ℝ A ∧
          (∀ i, labels A (u i) = labels A (u 0)) ∧
          (base = .spherical → ‖liftLabel A (labels A (u 0))‖ < 1) ∧
          0 < projectedDensity base f A (labels A (u 0)) ∧
          projectedDensity base f A (labels A (u 0)) ≠ ∞ ∧
          projectedDensity base f A (labels A (u 0)) =
            ballDensityVersion ν A (labels A (u 0)) ∧
          projectedDensity base f A (labels A (u 0)) =
            gaussianDensityVersion ν A (labels A (u 0)))

def haarRows (d ℓ : ℕ) : Measure (Rows d ℓ) :=
  (gaussianRows d ℓ).map (InnerProductSpace.gramSchmidtNormed ℝ)

def cmi {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (μ : Measure (Z × (X × Y))) [IsFiniteMeasure μ] : ℝ≥0∞ :=
  klDiv μ (μ.fst ⊗ₘ (μ.condKernel.fst ×ₖ μ.condKernel.snd))

def finiteEntropy {J : Type*} [Fintype J] [MeasurableSpace J] (μ : Measure J) : ℝ :=
  ∑ j, - μ.real {j} * Real.log (μ.real {j})

def stateMessageKernel {d k V W : ℕ} (κ : Kernel (Fin V × Data d k) (Fin W)) :
    Kernel ((Vec d × Fin V) × Rows d k) (Fin W) :=
  κ.comap (fun z => (z.1.2, (z.2, labels z.2 z.1.1))) (by unfold labels; fun_prop)

instance {d k V W : ℕ} (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    IsMarkovKernel (stateMessageKernel κ) := by
  unfold stateMessageKernel
  infer_instance

def stateMessageLaw {d k V W : ℕ} (q : Measure (Vec d × Fin V))
    (κ : Kernel (Fin V × Data d k) (Fin W)) : Measure ((Vec d × Fin V) × Fin W) :=
  (((q.prod (gaussianRows d k)) ⊗ₘ stateMessageKernel κ).map
    (fun z => (z.1.1, z.2)))

instance {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    IsProbabilityMeasure (stateMessageLaw q κ) := by
  unfold stateMessageLaw
  infer_instance

def stateHaarSideLaw {d V W : ℕ} (ℓ : ℕ)
    (q : Measure ((Vec d × Fin V) × Fin W)) :
    Measure ((Fin V × Data d ℓ) × (Vec d × Fin W)) :=
  ((haarRows d ℓ).prod q).map
    (fun z => ((z.2.1.2, (z.1, labels z.1 z.2.1.1)), (z.2.1.1, z.2.2)))

instance {d V W : ℕ} (ℓ : ℕ)
    (q : Measure ((Vec d × Fin V) × Fin W)) [IsFiniteMeasure q] :
    IsFiniteMeasure (stateHaarSideLaw ℓ q) := by
  unfold stateHaarSideLaw haarRows
  infer_instance

def terminalConditionalEntropy {d V W : ℕ}
    (q : Measure ((Vec d × Fin V) × Fin W)) : ℝ :=
  finiteEntropy (q.map (fun z => (z.1.2, z.2))) - finiteEntropy (q.map (fun z => z.1.2))

def HaarReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 64 ≤ d →
    ∀ (V W : ℕ) [NeZero V] [NeZero W]
      (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q],
      q.fst = sphereLaw d →
      ∀ (κ : Kernel (Fin V × Data d (d / 16)) (Fin W)) [IsMarkovKernel κ],
        cmi (stateHaarSideLaw (d / 4) (stateMessageLaw q κ)) ≤
          ENNReal.ofReal (terminalConditionalEntropy (stateMessageLaw q κ) /
            ((d / 16 + 1 : ℕ) : ℝ) + C * (d : ℝ) +
            Real.log (1 + C * (d : ℝ) + finiteEntropy q.snd) +
            C * (finiteEntropy q.snd + Real.log (d : ℝ)) / (d : ℝ)^2)

end PosteriorReplicas
end
end

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

universe u

namespace PosteriorRegression

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

namespace Learner

abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)

def angularError {d : ℕ} (s ŝ : UnitSphere d) : ℝ :=
  Real.arccos ⟪ŝ.val, s.val⟫

end Learner

end PosteriorRegression

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix
open scoped ENNReal NNReal RealInnerProductSpace Classical

noncomputable section

namespace PosteriorRegression
abbrev CompletedObservation (d : ℕ) := NullMeasurableSpace (Vector d × ℝ) (observationReference d)
abbrev Destination (M : ℕ) := Bool × State M

structure CompletedKernelLearner (d M : ℕ) where
  initial : Measure (Destination M)
  initial_probability : IsProbabilityMeasure initial
  transition : ℕ → State M → Kernel (CompletedObservation d) (Destination M)
  transition_markov : ∀ t a, IsMarkovKernel (transition t a)
  output : ℕ → State M → Measure (UnitSphere d)
  output_probability : ∀ t a, IsProbabilityMeasure (output t a)

attribute [instance] CompletedKernelLearner.initial_probability
  CompletedKernelLearner.transition_markov CompletedKernelLearner.output_probability

namespace CompletedKernelLearner
open Learner
def destStatus {M : ℕ} (n : ℕ) (v : Destination M) : RunStatus M :=
  if v.1 then Sum.inr (n,v.2) else Sum.inl v.2

def finishState {M : ℕ} (T : ℕ) : RunStatus M → ℕ × State M
  | .inl a => (T,a)
  | .inr done => done

def stepMeasure {d M T : ℕ} (K : CompletedKernelLearner d M)
    (s : UnitSphere d) (x : Samples d T) (i : Fin T) : RunStatus M → Measure (RunStatus M)
  | .inr done => Measure.dirac (.inr done)
  | .inl a => (K.transition (i.val+1) a (x i,⟪x i,s.val⟫)).map (destStatus (i.val+1))

def runMeasure {d M T : ℕ} (K : CompletedKernelLearner d M)
    (s : UnitSphere d) (x : Samples d T) : ℕ → Measure (RunStatus M)
  | 0 => K.initial.map (destStatus 0)
  | n+1 => if hn : n<T then (K.runMeasure s x n).bind (K.stepMeasure s x ⟨n,hn⟩)
      else K.runMeasure s x n

def terminalLaw {d M T : ℕ} (K : CompletedKernelLearner d M)
    (s : UnitSphere d) (x : Samples d T) : Measure (ℕ × State M) :=
  (K.runMeasure s x T).map (finishState T)

def estimateLaw {d M T : ℕ} (K : CompletedKernelLearner d M)
    (s : UnitSphere d) (x : Samples d T) : Measure (UnitSphere d) :=
  (K.terminalLaw s x).bind (fun a => K.output a.1 a.2)

end CompletedKernelLearner

structure JointKernelExperiment (d M T : ℕ) (Ω : Type u) [MeasurableSpace Ω]
    (ρ : Measure Ω) where
  rules : Ω → CompletedKernelLearner d M
  outputKernel : Kernel (Ω × (UnitSphere d × Samples d T)) (UnitSphere d)
  output_markov : IsMarkovKernel outputKernel
  conditional_output : ∀ᵐ ω ∂ρ, ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)),
    outputKernel (ω,z) = (rules ω).estimateLaw z.1 z.2

attribute [instance] JointKernelExperiment.output_markov

namespace JointKernelExperiment
open Learner
def law {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω] {ρ : Measure Ω}
    (E : JointKernelExperiment d M T Ω ρ) : Measure ((Ω × (UnitSphere d × Samples d T)) × UnitSphere d) :=
  (ρ.prod ((uniformSphere d).prod (sampleLaw d T))) ⊗ₘ E.outputKernel

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω] {ρ : Measure Ω}
    (E : JointKernelExperiment d M T Ω ρ) (ε : ℝ) : ℝ≥0∞ :=
  E.law {z | angularError z.1.2.1 z.2 ≤ ε}

end JointKernelExperiment

def KernelSubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0<ε → ε≤1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ E : JointKernelExperiment d (M d) T Ω ρ,
    (2/3 : ℝ≥0∞) ≤ E.uniformSuccess ε →
    c * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ)

end PosteriorRegression

namespace PosteriorReplicas

end PosteriorReplicas
end
end

namespace PosteriorReplicas

universe u

def source_main_statement : Prop :=
  EqualLabelMeasureIdentity ∧ EqualLabelVersions ∧
    GaussianReplicaBlock ∧ DistanceReplicaBlock ∧ HaarReplicaBlock ∧
    SyntheticReplicaBlock ∧ IncidenceReplicaBlock ∧
    PosteriorRegression.KernelSubquadraticMemory.{u}

end PosteriorReplicas

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.PosteriorReplicas.source_main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/140.md: In noiseless Gaussian regression, a learner observes inner products of an unknown unit vector in $\mathbb R^d$ with independent standard Gaussian vectors. The formalization proves that, for every fixed $A>0$, there is $c_A>0$ such that, in sufficiently large dimension, a learner retaining at most $Ad^2$ bits between observations needs at least $c_A d\log(1/\varepsilon)$ observations to attain angular error at most $\varepsilon$ with probability at least $2/3$ for a uniformly random unit signal, for $0<\varepsilon\le1/10$. For memory $o(d^2)$, the constant can be universal, and the selected statement also permits success at least $2/3$ separately for every signal. The linked supporting results include inverse Gram-matrix moments, exact-projection densities, regularization bounds, and sphere- and cube-prior block estimates. The paper studies how posterior replicas—independent signals drawn conditionally on the same observed data—control information in noiseless Gaussian regression. The formalization establishes the equal-label identity for finite measures, its density and measurable forms, and information bounds for Gaussian, distance, Haar, synthetic, and incidence comparisons. These statements retain exact observation labels, independent side randomness, and randomized transition rules. For a learner using $M(d)=o(d^2)$ bits of memory, the resulting bound says that, for sufficiently large $d$ and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform unit-sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations, where $c>0$ is universal. The formalized streaming result uses the $2/3$ threshold; the stronger $3/5$ variant is outside this scope. The formalization controls information gained from exact Gaussian observations of a spherical image of the uniform cube. Under the stated entropy and size conditions, repeated localization over $t$ observation blocks produces nested disclosures with mutual information at most $C(n+1)t$ and expected final localization level at most $Ct$. The selected estimates include inverse-volume control, kernel coercivity, and drift for the actual observation rows. For a law of finite relative entropy with respect to a uniform cell law in sufficiently large dimension, the regularization procedure terminates almost surely in regular cells. Its expected depth and number of attempts are finite, with at most twice one plus the expected depth in expectation; the remaining relative entropy plus $(\log 2)n/4$ times the expected depth is at most the initial relative entropy plus $2/e$. The paper uses projection moments and domination by positive spherical caps to bound the information carried by exact Gaussian observations of an unknown unit vector. The formalization covers integrated frame and sphere moments, cap domination, Riesz-density estimates with fixed offsets, and bounds valid at every radius. It also covers probability bounds for finite-memory learners at a fixed stopping time and after summing over stopping times. For $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior requires $T\ge c d\log(1/\varepsilon)$ observations for a universal $c>0$. A corresponding bound holds when $M\le A d^2$ for each fixed $A>0$, with the constant allowed to depend on $A$. The randomized learner model allows independent shared seeds; its reduction to a finite-state model is proved for dimensions at least three, with the auxiliary dimension-two case outside this scope. The paper compares fresh Gaussian observations with observations coupled to information already held in memory. The formalization covers mixed-moment and actual-row estimates, critical-radius, one-level, and two-label comparisons, and conditional-information bounds across a block of observations. For sufficiently large dimension $d$, the relevant entropy bounds of order $d^2$ bound the information in the fresh experiment by that in the coupled experiment plus a term of order $d$; the associated block information increase also has order $d$. It also covers two-point identities on observation fibers and the fiber-block bound, including the boundary case of $d-2$ observed rows. The uniform unit-sphere prior, Gaussian rows, finite memory states, and randomized transition rules remain part of these statements. The separate streaming consequences and several intermediate comparison constructions are outside this selection. The paper uses subspheres to bound the number of exact Gaussian observations needed to estimate a unit vector with limited memory. The formalization proves that, for $M(d)=o(d^2)$ bits of memory, sufficiently large $d$, and $0<\varepsilon\le1/10$, success probability at least $2/3$ under the uniform sphere prior, or for every unit signal, requires at least $2^{-16}d\log_2(1/\varepsilon)$ observations. Under the uniform prior, a lower bound of the same order with a universal positive constant holds at success probability $1/2$. The formalization also covers radius-weighted block and terminal estimates, affine and dimension estimates, and a vector-valued beta-mixture comparison with its boundary cases. These statements retain their dimension, width, radius, and suffix hypotheses, as well as the finite-state learner's independent randomness and restrictions on stopping and output. -/
