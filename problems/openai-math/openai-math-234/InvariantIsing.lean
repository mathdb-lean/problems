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

- problem_id: InvariantIsing
- collection: openai-math
- question_id: openai-math:234
- source: openai-math
- source_locator: lean/ComparatorChallenges/InvariantIsing.lean#OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives an exact variational formula for the limiting pressure of orthogonally invariant Ising spin glasses at every fixed temperature, both almost surely and in expectation. The coupling matrix is a Haar-random rotation of a deterministic spectrum converging to a compactly supported law, with extreme eigenvalues converging to its support edges. The zero-field ground-state energy follows as temperature tends to zero. ([Lean](lean/docs/234.md)) We determine the limiting pressure of an Ising spin glass with Haar orthogonal eigenvectors, a compact limiting spectral law, and no asymptotic outliers, at every fixed temperature. The pressure converges in expectation and almost surely to a variational formula. We also give the limiting pressure with deterministic external fields whose empirical laws converge in first-moment transport distance, and derive a formula for the zero-field ground-state energy by taking temperature to zero.
- notes: OpenAI math result family 234, All-temperature pressure of orthogonally invariant Ising spin glasses -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/234.md
- track: solved
- answer_shape: proof
- context_lemmas: orthogonal_mulVec_norm_sq finiteSpectralMeasure_probability empiricalSpectralWeight_sum
- source_theorem: OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional OAI.InvariantIsing.positive_temperature_pressure_unconditional OAI.InvariantIsing.ground_state_limit_unconditional OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional OAI.InvariantIsing.random_pressure_limit_unconditional OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional
- source_theorem_count: 11
- source_solution_module: OAI.Probability.InvariantIsing.Unconditional
- source_papers: preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf
- source_scope_note: lean/docs/234.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! All-temperature invariant Ising pressure and its magnetic, random-spectral,
ground-state, and Gaussian-pattern extensions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Matrix Classical ENNReal
universe u
namespace InvariantIsing

abbrev Spin (N : ℕ) := Fin N → Bool

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def logPartition {X : Type*} [Fintype X] (H : X → ℝ) : ℝ :=
  Real.log ((Fintype.card X : ℝ)⁻¹ * ∑ x, Real.exp (H x))

def fieldEnergy {N : ℕ} (c : Fin N → ℝ) (σ : Spin N) : ℝ :=
  ∑ i, c i * spinValue (σ i)

abbrev Rotation (N : ℕ) :=
  EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)

abbrev Orthogonal (N : ℕ) := Matrix.orthogonalGroup (Fin N) ℝ

def spinVector {N : ℕ} (σ : Spin N) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => spinValue (σ i))

def rotatedEnergy {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (σ : Spin N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, eig i * (U (spinVector σ) i) ^ 2

def rotatedPressure {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

lemma orthogonal_mulVec_norm_sq {N : ℕ} (U : Orthogonal N)
    (v : EuclideanSpace ℝ (Fin N)) :
    ‖WithLp.toLp 2 ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ v.ofLp)‖ ^ 2 = ‖v‖ ^ 2 := by
  have hU : (U : Matrix (Fin N) (Fin N) ℝ)ᵀ *
      (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp U.property
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [pow_two]
  change ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ v.ofLp) ⬝ᵥ
      ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ v.ofLp) = v.ofLp ⬝ᵥ v.ofLp
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec]

def matrixRotation {N : ℕ} (U : Orthogonal N) : Rotation N :=
  { ((WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).trans
      (Matrix.UnitaryGroup.toLinearEquiv U)).trans
      (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm with
    norm_map' := fun v => (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (orthogonal_mulVec_norm_sq U v) }

structure OverlapPath where
  val : ℝ → ℝ
  monotone : Monotone val
  nonneg : ∀ s, 0 ≤ val s
  le_one : ∀ s, val s ≤ 1

instance : CoeFun OverlapPath (fun _ => ℝ → ℝ) := ⟨OverlapPath.val⟩

def pathMeasure : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

def deficit (p : OverlapPath) (r : ℝ) : ℝ :=
  1 - r - ∫ s, max (p s - r) 0 ∂pathMeasure

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def gaussianOperator (a v : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  if a = 0 then ∫ g, f (z + Real.sqrt v * g) ∂gaussianReal 0 1
  else a⁻¹ * Real.log (∫ g, Real.exp (a * f (z + Real.sqrt v * g)) ∂gaussianReal 0 1)

structure FieldStep where
  depth : ℕ
  cut : Fin (depth + 2) → ℝ
  ordered_cut : StrictMono cut
  first : cut 0 = 0
  last : cut (Fin.last (depth + 1)) = 1
  height : Fin (depth + 1) → ℝ
  nonneg : ∀ i, 0 ≤ height i
  ordered_height : Monotone height

def fieldFunction (h : FieldStep) (s : ℝ) : ℝ :=
  ∑ i : Fin (h.depth + 1),
    if h.cut i.castSucc < s ∧ s < h.cut i.succ then h.height i else 0

def fieldIncrement (h : FieldStep) (i : Fin (h.depth + 1)) : ℝ × ℝ :=
  (h.cut i.castSucc, h.height i -
    if hi : i.val = 0 then 0 else h.height ⟨i.val - 1, by omega⟩)

def fieldValue (h : FieldStep) (b : ℝ) : ℝ :=
  ((List.ofFn (fieldIncrement h)).foldr
    (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z))) b -
    h.height (Fin.last h.depth) / 2

def fieldPairing (p : OverlapPath) (h : FieldStep) : ℝ :=
  ∫ s, p s * fieldFunction h s ∂pathMeasure

def entropyFunctional (p : OverlapPath) : EReal :=
  ⨆ h : FieldStep, ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)

def spectralFunctional (R : ℝ → ℝ) (p : OverlapPath) : ℝ :=
  (1 / 2 : ℝ) * ∫ r, R (deficit p r) ∂pathMeasure

def variationalFunctional (R : ℝ → ℝ) : EReal :=
  ⨅ p : OverlapPath, entropyFunctional p + (spectralFunctional R p : EReal)

def measureResolvent (μ : Measure ℝ) (b : ℝ) : ℝ := ∫ y, 1 / (b - y) ∂μ

def measureInverse (μ : Measure ℝ) (e x : ℝ) : ℝ :=
  if h : ∃ b, e < b ∧ measureResolvent μ b = x then h.choose else e

def measureR (μ : Measure ℝ) (e x : ℝ) : ℝ :=
  if 0 < x then measureInverse μ e x - 1 / x else ∫ y, y ∂μ

def finiteSpectralMeasure {ι : Type*} (ρ eig : ι → ℝ) : Measure ℝ :=
  Measure.sum fun a => ENNReal.ofReal (ρ a) • Measure.dirac (eig a)

theorem finiteSpectralMeasure_probability {ι : Type*} [Fintype ι] (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1) :
    IsProbabilityMeasure (finiteSpectralMeasure ρ eig) := by
  apply HasSum.isProbabilityMeasure_sum_dirac hρ
  simpa only [hsum] using hasSum_fintype ρ

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

lemma empiricalSpectralWeight_sum {N : ℕ} (hN : 0 < N) :
    ∑ _i : Fin N, (1 : ℝ)/N=1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

def empiricalSpectralLaw {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) : ProbabilityMeasure ℝ :=
  ⟨finiteSpectralMeasure (fun _ => (1 : ℝ)/N) eig,
    finiteSpectralMeasure_probability _ _ (fun _ => by positivity) (empiricalSpectralWeight_sum hN)⟩

def spectralMinimum {n : ℕ} (eig : Fin (n+1) → ℝ) : ℝ :=
  (Finset.univ.image eig).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)

def spectralMaximum {n : ℕ} (eig : Fin (n+1) → ℝ) : ℝ :=
  (Finset.univ.image eig).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

def magneticBiasObjective (h : FieldStep) (s b : ℝ) : ℝ := fieldValue h b - b * s

def constrainedFieldValue (h : FieldStep) (s : ℝ) : ℝ :=
  sInf (range (magneticBiasObjective h s))

def magneticGroupValue {A : Type*} [Fintype A] (γ m : A → ℝ) (h : FieldStep) : ℝ :=
  ∑ a, γ a * constrainedFieldValue h (m a)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def magneticEntropyFunctional {A : Type*} [Fintype A] (γ m : A → ℝ)
    (p : OverlapPath) : EReal :=
  ⨆ h : FieldStep, ((magneticGroupValue γ m h + fieldPairing p h / 2 : ℝ) : EReal)

def magneticVariationalFunctional {A : Type*} [Fintype A] (R : ℝ → ℝ) (γ m : A → ℝ) : EReal :=
  ⨅ p : OverlapPath, magneticEntropyFunctional γ m p + (spectralFunctional R p : EReal)

def RationalMagnetization (A : Type*) := {m : A → ℚ // ∀ a, |(m a : ℝ)| < 1}

def finiteMagneticFunctional {A : Type*} [Fintype A] (R : ℝ → ℝ) (γ c : A → ℝ) : EReal :=
  ⨆ m : RationalMagnetization A,
    ((∑ a, γ a * c a * (m.val a : ℝ) : ℝ) : EReal) +
      magneticVariationalFunctional R γ (fun a => (m.val a : ℝ))

def finiteIndexWeight {Ω A : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → A) (a : A) : ℝ := P.real (g ⁻¹' {a})

def simpleFieldIndex {Ω : Type*} [MeasurableSpace Ω] (s : SimpleFunc Ω ℝ) (x : Ω) : s.range :=
  ⟨s x,s.mem_range_self x⟩

def simpleFieldWeight {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : SimpleFunc Ω ℝ) :=
  finiteIndexWeight P (simpleFieldIndex s)

abbrev SimpleFieldPositive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : SimpleFunc Ω ℝ) :=
  {i : s.range // 0 < simpleFieldWeight P s i}

def simpleFieldValue {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) (R : ℝ → ℝ) : ℝ :=
  (finiteMagneticFunctional R (fun i : SimpleFieldPositive P s => simpleFieldWeight P s i)
    (fun i => i.val.val)).toReal

def fieldSimpleApproximation (n : ℕ) : SimpleFunc ℝ ℝ :=
  SimpleFunc.approxOn id measurable_id (range (id : ℝ → ℝ) ∪ {0}) 0 (by simp) n

def magneticFieldFunctional (spectral : Measure ℝ) (edge : ℝ) (field : ProbabilityMeasure ℝ) : ℝ :=
  limUnder atTop (fun n => simpleFieldValue (field : Measure ℝ) (fieldSimpleApproximation n)
    (measureR spectral edge))

structure FieldLawCoupling (μ ν : ProbabilityMeasure ℝ) where
  law : ProbabilityMeasure (ℝ × ℝ)
  fst : (law : Measure (ℝ × ℝ)).map Prod.fst = (μ : Measure ℝ)
  snd : (law : Measure (ℝ × ℝ)).map Prod.snd = (ν : Measure ℝ)

def FieldLawCoupling.cost {μ ν : ProbabilityMeasure ℝ} (p : FieldLawCoupling μ ν) : ℝ≥0∞ :=
  ∫⁻ xy, ENNReal.ofReal |xy.1-xy.2| ∂(p.law : Measure (ℝ × ℝ))

def fieldWassersteinOne (μ ν : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  ⨅ p : FieldLawCoupling μ ν, p.cost

def scaledSpectralLaw (ν : ProbabilityMeasure ℝ) (β : ℝ) : ProbabilityMeasure ℝ :=
  ν.map (fun x => β*x)

def groundStateEnergy {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N) : ℝ :=
  (N : ℝ)⁻¹ * Finset.univ.sup' Finset.univ_nonempty (rotatedEnergy eig U)

def thermalVariationalValue (ν : ProbabilityMeasure ℝ) (b β : ℝ) : ℝ :=
  (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal/β

abbrev FieldSpectralData (N : ℕ) := (Fin N → ℝ) × (Fin N → ℝ)

def dataPhysicalPressure {N : ℕ} (d : FieldSpectralData N) (U : Orthogonal N) : ℝ :=
  rotatedPressure d.1 (matrixRotation U⁻¹) d.2

def ConditionalFieldOrbitLaw {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (d : Ω → FieldSpectralData N) (pressure : Ω → ℝ)
    (H : Measure (Orthogonal N)) : Prop :=
  P.map (fun ω => (d ω,pressure ω)) =
    ((P.map d).prod H).map (fun z => (z.1,dataPhysicalPressure z.1 z.2))

def spectralExcess {N : ℕ} (eig : Fin N → ℝ) (a b : ℝ) : ℝ :=
  (insert 0 (Finset.univ.image (fun i => max (a-eig i) (eig i-b)))).max'
    (Finset.insert_nonempty 0 _)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

@[irreducible] def gaussianPatternCount (α : ℝ) (N : ℕ) : ℕ := ⌊α*N⌋₊

def marchenkoPasturA (α : ℝ) : ℝ := (1-Real.sqrt α)^2

def marchenkoPasturB (α : ℝ) : ℝ := (1+Real.sqrt α)^2

def marchenkoPasturLower (α : ℝ) : ℝ := if α ≤ 1 then 0 else marchenkoPasturA α

def marchenkoPasturMeasure (α : ℝ) : Measure ℝ :=
  ENNReal.ofReal (max (1-α) 0) • Measure.dirac 0 +
    volume.withDensity ((Icc (marchenkoPasturA α) (marchenkoPasturB α)).indicator
      (fun x => ENNReal.ofReal
        (Real.sqrt ((marchenkoPasturB α-x)*(x-marchenkoPasturA α))/(2*Real.pi*x))))

def gaussianPatternLimit (α c : ℝ) : ℝ :=
  (variationalFunctional (measureR ((marchenkoPasturMeasure α).map (fun x => c*x))
    (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α)))).toReal

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def gaussianPatternArray {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    Matrix (Fin N) (Fin m) ℝ := fun i j => z (i,j)

def gaussianPatternSum {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) (σ : Spin N) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 ((gaussianPatternArray z)ᵀ *ᵥ (fun i => spinValue (σ i)))

def gaussianPatternPressure {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  (N : ℝ)⁻¹*logPartition (fun σ : Spin N => c/(2*N)*‖gaussianPatternSum z σ‖^2)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def gaussianPatternGroundEnergy {N m : ℕ} (ε : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  (N : ℝ)⁻¹*Finset.univ.sup' Finset.univ_nonempty
    (fun σ : Spin N => ε/(2*N)*‖gaussianPatternSum z σ‖^2)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def gaussianPatternColumn {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (i : Fin N) : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => z (i,j))

def gaussianPatternOperator {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    ((gaussianPatternArray z)ᵀ.mulVecLin.toContinuousLinearMap)

def limiting_pressure_of_extreme_limits_unconditional_statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (_hU : ∀ N, Measurable (U N))
    (_hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hmin : Tendsto (fun k => spectralMinimum (eig (k+1))) atTop (𝓝 a))
    (_hmax : Tendsto (fun k => spectralMaximum (eig (k+1))) atTop (𝓝 b))
    (_hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)),
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun _ => 0))
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal)

def limiting_wasserstein_field_pressure_of_extreme_limits_unconditional_statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (_hU : ∀ N, Measurable (U N))
    (_hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hmin : Tendsto (fun k => spectralMinimum (eig (k+1))) atTop (𝓝 a))
    (_hmax : Tendsto (fun k => spectralMaximum (eig (k+1))) atTop (𝓝 b))
    (_hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν))
    (field : (N : ℕ) → Fin N → ℝ) (ξ : ProbabilityMeasure ℝ)
    (_hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ))
    (_hw : Tendsto (fun k => fieldWassersteinOne (empiricalSpectralLaw (Nat.succ_pos k) (field (k+1))) ξ)
      atTop (𝓝 0)),
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N) ∂P)
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N))
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ))

def positive_temperature_pressure_unconditional_statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (_hU : ∀ N, Measurable (U N))
    (_hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (β : ℝ) (_hβ : 0 < β)
    (_hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)),
    Tendsto (fun N => ∫ ω, rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)
      atTop (𝓝 (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0))
      atTop (𝓝 (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal)

def ground_state_limit_unconditional_statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (_hU : ∀ N, Measurable (U N))
    (_hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (_hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)),
    ∃ M : ℝ,
      Tendsto (fun N => ∫ ω, groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹) ∂P)
        atTop (𝓝 M) ∧
      (∀ᵐ ω ∂P, Tendsto (fun N => groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹))
        atTop (𝓝 M)) ∧
      Tendsto (thermalVariationalValue ν b) atTop (𝓝 M)

def random_pressure_tendsto_in_measure_unconditional_statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ) (heig : ∀ N, Measurable (eig N)) (hY : ∀ N, Measurable (Y N)) (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)] [∀ N, (H N).IsMulRightInvariant] (hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N)) (ν : ProbabilityMeasure ℝ) (a b : ℝ) (hcompact : IsCompact (ν : Measure ℝ).support) (hbound : (ν : Measure ℝ).support ⊆ Icc a b) (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support) (hweak : TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω))) atTop
      (fun _ => LevyProkhorov.ofMeasure ν)) (hexcess : TendstoInMeasure P (fun k ω => spectralExcess (eig (k+1) ω) a b)
      atTop (fun _ => 0)),
    TendstoInMeasure P (fun k => Y (k+1)) atTop
      (fun _ => (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal)

def random_pressure_limit_unconditional_statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (_heig : ∀ N, Measurable (eig N)) (_hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (_hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hweak : TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω))) atTop
      (fun _ => LevyProkhorov.ofMeasure ν))
    (_hexcess : TendstoInMeasure P (fun k ω => spectralExcess (eig (k+1) ω) a b)
      atTop (fun _ => 0))
    (_hUI : UniformIntegrable (fun k => Y (k+1)) 1 P),
    TendstoInMeasure P (fun k => Y (k+1)) atTop
      (fun _ => (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) ∧
    Tendsto (fun k => eLpNorm (fun ω => Y (k+1) ω-
      (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, Y (k+1) ω ∂P) atTop
      (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal)

def random_pressure_tendsto_ae_unconditional_statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (_heig : ∀ N, Measurable (eig N)) (_hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (_hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hno : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ i, a-ε ≤ eig N ω i ∧ eig N ω i ≤ b+ε)
    (_hweak : ∀ᵐ ω ∂P, Tendsto (fun k =>
      empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω)) atTop (𝓝 ν)),
    ∀ᵐ ω ∂P, Tendsto (fun N => Y N ω) atTop
      (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal)

def random_field_pressure_tendsto_ae_unconditional_statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : (N : ℕ) → Ω → FieldSpectralData N) (Y : ℕ → Ω → ℝ)
    (_hd : ∀ N, Measurable (d N)) (_hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (_hlaw : ∀ N, ConditionalFieldOrbitLaw P (d N) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hno : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ i, a-ε ≤ (d N ω).1 i ∧ (d N ω).1 i ≤ b+ε)
    (_hweak : ∀ᵐ ω ∂P, Tendsto (fun k =>
      empiricalSpectralLaw (Nat.succ_pos k) (d (k+1) ω).1) atTop (𝓝 ν))
    (ξ : ProbabilityMeasure ℝ) (_hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ))
    (_hw : ∀ᵐ ω ∂P, Tendsto (fun k => fieldWassersteinOne
      (empiricalSpectralLaw (Nat.succ_pos k) (d (k+1) ω).2) ξ) atTop (𝓝 0)),
    ∀ᵐ ω ∂P, Tendsto (fun N => Y N ω) atTop
      (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ))

def gaussianPattern_pressure_limit_unconditional_statement : Prop :=
  ∀ (α : ℝ) (_hα : 0 < α)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (_hZ : ∀ N, Measurable (Z N)) (_hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (c : ℝ),
    TendstoInMeasure P (fun k ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)) atTop
      (fun _ => gaussianPatternLimit α c) ∧
    Tendsto (fun k => eLpNorm (fun ω => gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω)-
      gaussianPatternLimit α c) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, gaussianPatternPressure (N := k+1) (m := gaussianPatternCount α (k+1)) c (Z (k+1) ω) ∂P) atTop
      (𝓝 (gaussianPatternLimit α c))

def gaussianPattern_ground_limit_unconditional_statement : Prop :=
  ∀ (α : ℝ) (_hα : 0 < α)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (_hZ : ∀ N, Measurable (Z N)) (_hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P)
    (ε : ℝ),
    ∃ e : ℝ,
      TendstoInMeasure P (fun k ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)) atTop (fun _ => e) ∧
      Tendsto (fun k => eLpNorm (fun ω => gaussianPatternGroundEnergy ε (Z (k+1) ω)-e) 1 P)
        atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ ω, gaussianPatternGroundEnergy ε (Z (k+1) ω) ∂P) atTop (𝓝 e) ∧
      Tendsto (fun β => gaussianPatternLimit α (ε*β)/β) atTop (𝓝 e)

def gaussianPattern_norm_limits_unconditional_statement : Prop :=
  ∀ (α : ℝ) (_hα : 0 < α)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (_hZ : ∀ N, Measurable (Z N)) (_hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P),
    ∃ eplus eminus : ℝ, 0 ≤ eplus ∧ eminus ≤ 0 ∧
      Tendsto (fun β => gaussianPatternLimit α β/β) atTop (𝓝 eplus) ∧
      Tendsto (fun β => gaussianPatternLimit α (-β)/β) atTop (𝓝 eminus) ∧
      (TendstoInMeasure P (fun k ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)) atTop
        (fun _ => Real.sqrt (2*eplus)) ∧
       Tendsto (fun k => eLpNorm (fun ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)-
        Real.sqrt (2*eplus)) 1 P) atTop (𝓝 0)) ∧
      (TendstoInMeasure P (fun k ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1))
        atTop (fun _ => Real.sqrt (-2*eminus)) ∧
       Tendsto (fun k => eLpNorm (fun ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1)-
          Real.sqrt (-2*eminus)) 1 P) atTop (𝓝 0))

end InvariantIsing

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1, u} : Prop :=
  _root_.OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional_statement.{u_1} ∧
  _root_.OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional_statement.{u_1} ∧
  _root_.OAI.InvariantIsing.positive_temperature_pressure_unconditional_statement.{u_1} ∧
  _root_.OAI.InvariantIsing.ground_state_limit_unconditional_statement.{u_1} ∧
  _root_.OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional_statement.{u_1} ∧
  _root_.OAI.InvariantIsing.random_pressure_limit_unconditional_statement.{u_1} ∧
  _root_.OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional_statement.{u_1} ∧
  _root_.OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional_statement.{u_1} ∧
  _root_.OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional_statement.{u} ∧
  _root_.OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional_statement.{u} ∧
  _root_.OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional_statement.{u}

end Problem

/- Formalization scope, from lean/docs/234.md: The formalization gives variational limits for orthogonally invariant Ising spin glasses whose eigenvectors have Haar law and whose empirical eigenvalue distributions converge to a compactly supported law with the stated control of extreme eigenvalues. The pressure converges both in expectation and almost surely to an explicit functional of the limiting spectral law. A version with external fields assumes convergence of their empirical laws in Wasserstein distance and gives the corresponding magnetic-field functional. The formalization also covers every positive temperature, a ground-state limit, random spectral data with the stated conditional Haar law, and Gaussian-pattern specializations. These hypotheses identify the invariant models to which the limits apply. -/
