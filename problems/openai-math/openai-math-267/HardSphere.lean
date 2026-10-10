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

- problem_id: HardSphere
- collection: openai-math
- question_id: openai-math:267
- source: openai-math
- source_locator: lean/ComparatorChallenges/HardSphere.lean#OAI.HardSphere.condensation_with_mixed
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Bose–Einstein condensation for the exact canonical Gibbs state of the three-dimensional hard-sphere gas: each fixed exclusion distance and sufficiently small fixed density admit a strictly positive temperature, independent of volume, with positive condensate fraction in the thermodynamic limit. At zero temperature, proves the Bogoliubov leading quantum-depletion law for hard spheres and fixed bounded nonnegative radial finite-range potentials of positive scattering length, taking the thermodynamic limit before the dilute limit. ([Lean](lean/docs/267.md)) We prove Bose–Einstein condensation in every ground state of a dilute three-dimensional hard-sphere Bose gas. At every sufficiently small fixed gas parameter, the constant orbital contains a positive fraction of the particles in the thermodynamic limit. The fraction can be chosen independently of the gas parameter, and the conclusion holds for arbitrary complex ground states.
- notes: OpenAI math result family 267, Positive-temperature Bose–Einstein condensation and exact quantum depletion -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/267.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.HardSphere.condensation_with_mixed
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.HardSphere.Main
- source_papers: preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf
- source_scope_note: lean/docs/267.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


/-!
# Ground-state condensation in the dilute hard-sphere gas

The main result covers all pure ground states and all density operators supported on
 the ground space. In particular it covers the normalized ground-space projection.
Only the definitions needed to state this result are retained below.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators InnerProductSpace ComplexOrder NNReal

namespace OAI.HardSphere

abbrev Length := {L : ℝ // 0 < L}

instance lengthPositive (L : Length) : Fact (0 < L.val) := ⟨L.property⟩

abbrev Torus (L : Length) := Fin 3 → AddCircle L.val

abbrev Configuration (N : ℕ) (L : Length) := Fin N → Torus L

abbrev LiftedConfiguration (N : ℕ) := Fin N → Fin 3 → ℝ

abbrev Direction (N : ℕ) := Fin N × Fin 3

def torusDistance (L : Length) (x y : Torus L) : ℝ :=
  Real.sqrt (∑ j : Fin 3, dist (x j) (y j) ^ 2)

def allowed (N : ℕ) (L : Length) (a : ℝ) : Set (Configuration N L) :=
  {X | ∀ i j : Fin N, i < j → a < torusDistance L (X i) (X j)}

def project (N : ℕ) (L : Length) (X : LiftedConfiguration N) : Configuration N L :=
  fun i j ↦ (X i j : AddCircle L.val)

def representative (N : ℕ) (L : Length) (X : Configuration N L) : LiftedConfiguration N :=
  fun i j ↦ (AddCircle.equivIco L.val 0 (X i j)).val

def coordDerivative (N : ℕ) (L : Length) (f : Configuration N L → ℂ)
    (p : Direction N) (X : Configuration N L) : ℂ :=
  fderiv ℝ (fun Y : LiftedConfiguration N ↦ f (project N L Y))
    (representative N L X) (Pi.single p.1 (Pi.single p.2 1))

abbrev ScalarL2 (N : ℕ) (L : Length) : Type :=
  Lp ℂ 2 (volume : Measure (Configuration N L))

abbrev Jet (N : ℕ) (L : Length) :=
  ScalarL2 N L × (Direction N → ScalarL2 N L)

structure SmoothTest (N : ℕ) (L : Length) (a : ℝ) where
  toFun : Configuration N L → ℂ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X : LiftedConfiguration N ↦ toFun (project N L X))
  compact : HasCompactSupport toFun
  support_allowed : tsupport toFun ⊆ allowed N L a
  memLp : MemLp toFun (2 : ℕ) (volume : Measure (Configuration N L))
  partial_memLp : ∀ p : Direction N, MemLp (coordDerivative N L toFun p) (2 : ℕ) volume

def SmoothTest.jet {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) : Jet N L :=
  (f.memLp.toLp f.toFun, fun p ↦ (f.partial_memLp p).toLp (coordDerivative N L f.toFun p))

def dirichletDomain (N : ℕ) (L : Length) (a : ℝ) : Set (Jet N L) :=
  closure (Set.range (SmoothTest.jet (N := N) (L := L) (a := a)))

def energy {N : ℕ} {L : Length} (u : Jet N L) : ℝ :=
  ∑ p : Direction N, ‖u.2 p‖ ^ 2

def bosonic {N : ℕ} {L : Length} (ψ : ScalarL2 N L) : Prop :=
  ∀ σ : Equiv.Perm (Fin N),
    (fun X : Configuration N L ↦ ψ (fun i ↦ X (σ i))) =ᵐ[volume] ψ

def IsGroundVector (N : ℕ) (L : Length) (a : ℝ) (u : Jet N L) : Prop :=
  u ∈ dirichletDomain N L a ∧ bosonic u.1 ∧ ‖u.1‖ = 1 ∧
    ∀ v ∈ dirichletDomain N L a, bosonic v.1 → ‖v.1‖ = 1 → energy u ≤ energy v

def insertFirst {N : ℕ} (hN : 0 < N) {L : Length}
    (x : Torus L) (Y : Configuration (N - 1) L) : Configuration N L :=
  fun i ↦ Fin.cons (α := fun _ ↦ Torus L) x Y (Fin.cast (Nat.sub_add_cancel (Nat.succ_le_of_lt hN)).symm i)

def occupation {N : ℕ} (hN : 0 < N) {L : Length} (ψ : ScalarL2 N L) : ℝ :=
  (L.val ^ 3)⁻¹ * ∫ Y : Configuration (N - 1) L,
    ‖∫ x : Torus L, ψ (insertFirst hN x Y)‖ ^ 2

namespace Density
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def basisSet : Set H := (exists_hilbertBasis (𝕜:=ℂ) (E:=H)).choose

def basis : HilbertBasis (basisSet H) ℂ H :=
  (exists_hilbertBasis (𝕜:=ℂ) (E:=H)).choose_spec.choose

structure Operator where
  toCLM : H →L[ℂ] H
  positive : 0≤toCLM
  trace_one : HasSum (fun i : basisSet H ↦ (inner ℂ (basis H i) (toCLM (basis H i))).re) 1

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def Operator.compressionTrace (T : Operator H) (A : H →L[ℂ] K) : ℝ :=
  let adjoint := DFunLike.coe (F := (H →L[ℂ] K) ≃ₗᵢ⋆[ℂ] K →L[ℂ] H)
    (β := fun _ ↦ K →L[ℂ] H) ContinuousLinearMap.adjoint A
  ∑' j : basisSet K,(inner ℂ (adjoint (basis K j)) (T.toCLM (adjoint (basis K j)))).re

end Density

namespace Orbital

def sliceIntegral {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) (Y : Configuration (N-1) L) : ℂ :=
  (Real.sqrt (L.val^3))⁻¹ • ∫x : Torus L,ψ (insertFirst hN x Y)

def map {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) : ScalarL2 (N-1) L := by
  have integral_mul_le_sqrt {X : Type} [MeasurableSpace X] {ν : Measure X} (f g : X → ℝ) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
      (hf0 : 0 ≤ᵐ[ν] f) (hg0 : 0 ≤ᵐ[ν] g) :
      ∫ x, f x * g x ∂ν ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) *
        Real.sqrt (∫ x, g x ^ 2 ∂ν) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two hf0 hg0 (by simpa using hf) (by simpa using hg)
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

  have integral_norm_sq_le {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℂ} (hf : MemLp f 2 ν) :
      (∫ x, ‖f x‖ ∂ν)^2 ≤ ν.real univ * ∫ x, ‖f x‖ ^ 2 ∂ν := by
    have h := integral_mul_le_sqrt (fun _ : X ↦ 1) (fun x ↦ ‖f x‖)
      (memLp_const (1 : ℝ)) hf.norm (Eventually.of_forall fun _ ↦ zero_le_one)
      (Eventually.of_forall fun _ ↦ norm_nonneg _)
    simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one] at h
    have ha : 0 ≤ ∫ x, ‖f x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
    have hm : 0 ≤ ∫ x, ‖f x‖^2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
    have hs := (sq_le_sq₀ ha (by positivity)).2 h
    simpa only [mul_pow, Real.sq_sqrt (measureReal_nonneg), Real.sq_sqrt hm] using hs

  have memLp_slices {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure X} {μ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure μ] {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
      ∀ᵐ y ∂μ, MemLp (fun x ↦ f (y,x)) 2 ν := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,
      (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae] with y hm hi
    exact (memLp_two_iff_integrable_sq_norm hm).2 hi

  have memLp_integral_norm {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure X} {μ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure μ] {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
      MemLp (fun y ↦ ∫ x, ‖f (y,x)‖ ∂ν) 2 μ := by
    have hm := hf.aestronglyMeasurable.norm.integral_prod_right'
    apply (memLp_two_iff_integrable_sq hm).2
    have hi := (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_left
    apply (hi.const_mul (ν.real univ)).mono' (hm.pow 2)
    filter_upwards [memLp_slices hf] with y hy
    change ‖(∫ x, ‖f (y,x)‖ ∂ν)^2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact integral_norm_sq_le hy

  have cons_preserving {n : ℕ} (L : Length) :
      MeasurePreserving (fun p : Configuration n L × Torus L ↦ Fin.cons (α:=fun _ ↦ Torus L) p.2 p.1)
        (volume.prod volume) volume := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
    have hh := h.comp (Measure.measurePreserving_swap (μ:= (volume : Measure (Configuration n L))) (ν:=volume))
    convert hh using 1; try rfl
    funext p i
    simp [MeasurableEquiv.piFinSuccAbove]

  have insertFirst_preserving {N : ℕ} (hN : 0<N) (L : Length) :
      MeasurePreserving (fun p : Torus L×Configuration (N-1) L ↦ insertFirst hN p.1 p.2)
        ((volume : Measure (Torus L)).prod volume) volume := by
    cases N with
    | zero => omega
    | succ n =>
      unfold insertFirst
      have h := (cons_preserving (n:=n) L).comp
        (Measure.measurePreserving_swap (μ:=(volume : Measure (Torus L))) (ν:=volume))
      convert h using 1 <;> simp [Function.comp_def]

  have bathFirst_preserving {N : ℕ} (hN : 0<N) (L : Length) :
      MeasurePreserving (fun p : Configuration (N-1) L×Torus L ↦ insertFirst hN p.2 p.1)
        ((volume : Measure (Configuration (N-1) L)).prod volume) volume :=
    (insertFirst_preserving hN L).comp (Measure.measurePreserving_swap)

  have ground_slice_memLp {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) :
      MemLp (fun p : Configuration (N-1) L×Torus L ↦ ψ (insertFirst hN p.2 p.1)) 2
        ((volume : Measure (Configuration (N-1) L)).prod volume) :=
    (Lp.memLp ψ).comp_measurePreserving (bathFirst_preserving hN L)

  have sliceIntegral_memLp {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) : MemLp (sliceIntegral hN ψ) 2 volume := by
    have hf := ground_slice_memLp hN ψ
    have ha := memLp_integral_norm hf
    have hh : MemLp (fun Y ↦ ∫x : Torus L,ψ (insertFirst hN x Y)) 2 volume := by
      refine ha.mono' hf.aestronglyMeasurable.integral_prod_right' ?_
      exact Eventually.of_forall fun Y ↦ norm_integral_le_integral_norm _
    exact hh.const_smul ((Real.sqrt (L.val^3))⁻¹ : ℝ)

  exact (sliceIntegral_memLp hN ψ).toLp (sliceIntegral hN ψ)

def continuous {N : ℕ} (hN : 0<N) {L : Length} : ScalarL2 N L →L[ℂ] ScalarL2 (N-1) L := by
  have scalar_norm_sq_integral {N : ℕ} {L : Length} (u : ScalarL2 N L) :
      ‖u‖^2 = ∫ X, ‖u X‖^2 := by
    rw [← real_inner_self_eq_norm_sq (F := ScalarL2 N L), L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]

  have volume_torus (L : Length) : (volume : Measure (Torus L)) Set.univ = ENNReal.ofReal (L.val^3) := by
    rw [volume_pi,Measure.pi_univ]
    simp only [AddCircle.measure_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      ENNReal.ofReal_pow L.property.le]

  have integral_mul_le_sqrt {X : Type} [MeasurableSpace X] {ν : Measure X} (f g : X → ℝ) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
      (hf0 : 0 ≤ᵐ[ν] f) (hg0 : 0 ≤ᵐ[ν] g) :
      ∫ x, f x * g x ∂ν ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) *
        Real.sqrt (∫ x, g x ^ 2 ∂ν) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two hf0 hg0 (by simpa using hf) (by simpa using hg)
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

  have integral_norm_sq_le {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℂ} (hf : MemLp f 2 ν) :
      (∫ x, ‖f x‖ ∂ν)^2 ≤ ν.real univ * ∫ x, ‖f x‖ ^ 2 ∂ν := by
    have h := integral_mul_le_sqrt (fun _ : X ↦ 1) (fun x ↦ ‖f x‖)
      (memLp_const (1 : ℝ)) hf.norm (Eventually.of_forall fun _ ↦ zero_le_one)
      (Eventually.of_forall fun _ ↦ norm_nonneg _)
    simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one] at h
    have ha : 0 ≤ ∫ x, ‖f x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
    have hm : 0 ≤ ∫ x, ‖f x‖^2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
    have hs := (sq_le_sq₀ ha (by positivity)).2 h
    simpa only [mul_pow, Real.sq_sqrt (measureReal_nonneg), Real.sq_sqrt hm] using hs

  have memLp_slices {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure X} {μ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure μ] {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
      ∀ᵐ y ∂μ, MemLp (fun x ↦ f (y,x)) 2 ν := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,
      (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae] with y hm hi
    exact (memLp_two_iff_integrable_sq_norm hm).2 hi

  have memLp_integral_norm {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure X} {μ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure μ] {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
      MemLp (fun y ↦ ∫ x, ‖f (y,x)‖ ∂ν) 2 μ := by
    have hm := hf.aestronglyMeasurable.norm.integral_prod_right'
    apply (memLp_two_iff_integrable_sq hm).2
    have hi := (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_left
    apply (hi.const_mul (ν.real univ)).mono' (hm.pow 2)
    filter_upwards [memLp_slices hf] with y hy
    change ‖(∫ x, ‖f (y,x)‖ ∂ν)^2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact integral_norm_sq_le hy

  have cons_preserving {n : ℕ} (L : Length) :
      MeasurePreserving (fun p : Configuration n L × Torus L ↦ Fin.cons (α:=fun _ ↦ Torus L) p.2 p.1)
        (volume.prod volume) volume := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
    have hh := h.comp (Measure.measurePreserving_swap (μ:= (volume : Measure (Configuration n L))) (ν:=volume))
    convert hh using 1; try rfl
    funext p i
    simp [MeasurableEquiv.piFinSuccAbove]

  have insertFirst_preserving {N : ℕ} (hN : 0<N) (L : Length) :
      MeasurePreserving (fun p : Torus L×Configuration (N-1) L ↦ insertFirst hN p.1 p.2)
        ((volume : Measure (Torus L)).prod volume) volume := by
    cases N with
    | zero => omega
    | succ n =>
      unfold insertFirst
      have h := (cons_preserving (n:=n) L).comp
        (Measure.measurePreserving_swap (μ:=(volume : Measure (Torus L))) (ν:=volume))
      convert h using 1 <;> simp [Function.comp_def]

  have bathFirst_preserving {N : ℕ} (hN : 0<N) (L : Length) :
      MeasurePreserving (fun p : Configuration (N-1) L×Torus L ↦ insertFirst hN p.2 p.1)
        ((volume : Measure (Configuration (N-1) L)).prod volume) volume :=
    (insertFirst_preserving hN L).comp (Measure.measurePreserving_swap)

  have ground_slice_memLp {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) :
      MemLp (fun p : Configuration (N-1) L×Torus L ↦ ψ (insertFirst hN p.2 p.1)) 2
        ((volume : Measure (Configuration (N-1) L)).prod volume) :=
    (Lp.memLp ψ).comp_measurePreserving (bathFirst_preserving hN L)

  have occupation_le_norm_sq {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) :
      occupation hN ψ≤‖ψ‖^2 := by
    have hLp := L.property
    let f := fun p : Configuration (N-1) L×Torus L ↦ ψ (insertFirst hN p.2 p.1)
    have hf : MemLp f 2 (volume.prod volume) := ground_slice_memLp hN ψ
    have ha := memLp_integral_norm hf
    have hc : MemLp (fun Y ↦ ‖∫x,f (Y,x)‖) 2 volume := by
      refine ha.mono' hf.aestronglyMeasurable.integral_prod_right'.norm ?_
      exact Eventually.of_forall fun Y ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
        exact norm_integral_le_integral_norm _
    have hi := (hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).integral_prod_left
    have hbound : (∫Y,‖∫x,f (Y,x)‖^2)≤(volume : Measure (Torus L)).real univ * ∫p,‖f p‖^2 ∂volume.prod volume := by
      calc
        _ ≤ ∫Y,(volume : Measure (Torus L)).real univ * ∫x,‖f (Y,x)‖^2 := by
          apply integral_mono_ae hc.integrable_sq (hi.const_mul _)
          filter_upwards [memLp_slices hf] with Y hY
          exact (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2).trans
            (integral_norm_sq_le hY)
        _ = _ := by rw [integral_const_mul,←integral_prod _ (hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0))]
    have hm : (∫p,‖f p‖^2 ∂volume.prod volume)=‖ψ‖^2 := by
      rw [scalar_norm_sq_integral]
      exact (bathFirst_preserving hN L).integral_comp
        (by
          cases N with
          | zero => omega
          | succ n =>
            convert (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm.measurableEmbedding.comp
              (MeasurableEquiv.prodComm (α:=Configuration n L) (β:=Torus L)).measurableEmbedding using 1 <;> try rfl
            funext p i
            simp [insertFirst,MeasurableEquiv.piFinSuccAbove,MeasurableEquiv.prodComm])
        (fun X ↦ ‖ψ X‖^2)
    rw [hm,Measure.real,volume_torus,ENNReal.toReal_ofReal (by positivity : 0≤L.val^3)] at hbound
    unfold occupation
    change (L.val^3)⁻¹*(∫Y,‖∫x,f (Y,x)‖^2)≤‖ψ‖^2
    calc
      _ ≤ (L.val^3)⁻¹*(L.val^3*‖ψ‖^2) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ L.property.ne'),one_mul]

  have map_ae {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) : (map hN ψ : Configuration (N-1) L→ℂ)=ᵐ[volume] sliceIntegral hN ψ := by
    unfold map
    exact MemLp.coeFn_toLp _

  have map_add {N : ℕ} (hN : 0<N) {L : Length} (f g : ScalarL2 N L) : map hN (f+g)=map hN f+map hN g := by
    apply Lp.ext
    have hp := (bathFirst_preserving hN L).quasiMeasurePreserving.tendsto_ae.eventually (Lp.coeFn_add f g)
    have hs := Measure.ae_ae_of_ae_prod hp
    filter_upwards [map_ae hN (f+g),map_ae hN f,map_ae hN g,Lp.coeFn_add (map hN f) (map hN g),hs,
      memLp_slices (ground_slice_memLp hN f),memLp_slices (ground_slice_memLp hN g)] with Y hh hf hg hsum hY hfi hgi
    rw [hh,hsum]
    change sliceIntegral hN (f+g) Y=(map hN f) Y+(map hN g) Y
    rw [hf,hg]
    unfold sliceIntegral
    rw [←smul_add,←integral_add (hfi.integrable (by norm_num)) (hgi.integrable (by norm_num))]
    congr 1
    apply integral_congr_ae
    exact hY

  have map_smul {N : ℕ} (hN : 0<N) {L : Length} (c : ℂ) (f : ScalarL2 N L) : map hN (c • f)=c • map hN f := by
    apply Lp.ext
    have hp := (bathFirst_preserving hN L).quasiMeasurePreserving.tendsto_ae.eventually (Lp.coeFn_smul c f)
    have hs := Measure.ae_ae_of_ae_prod hp
    filter_upwards [map_ae hN (c•f),map_ae hN f,Lp.coeFn_smul c (map hN f),hs] with Y hh hf hc hY
    rw [hh,hc]
    change sliceIntegral hN (c•f) Y=c • (map hN f) Y
    rw [hf]
    change (Real.sqrt (L.val^3))⁻¹ • (∫x : Torus L,(c•f) (insertFirst hN x Y))=
      c • ((Real.sqrt (L.val^3))⁻¹ • ∫x : Torus L,f (insertFirst hN x Y))
    rw [integral_congr_ae hY]
    simp only [Pi.smul_apply]
    rw [integral_smul]
    exact smul_comm _ _ _

  have map_norm_sq {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) : ‖map hN ψ‖^2=occupation hN ψ := by
    have hLp := L.property
    rw [scalar_norm_sq_integral]
    have hsi := integral_congr_ae ((map_ae hN ψ).fun_comp fun x ↦ ‖x‖^2)
    simp only [Function.comp_def] at hsi
    rw [hsi]
    unfold sliceIntegral occupation
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,
      integral_const_mul,Real.sq_sqrt (by positivity : 0≤L.val^3)]

  have map_norm_le {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) : ‖map hN ψ‖≤‖ψ‖ := by
    have hh := (map_norm_sq hN ψ).trans_le (occupation_le_norm_sq hN ψ)
    nlinarith [norm_nonneg (map hN ψ),norm_nonneg ψ]

  exact ({ toFun := map hN, map_add' := map_add hN, map_smul' := map_smul hN } : ScalarL2 N L →ₗ[ℂ] ScalarL2 (N-1) L).mkContinuous 1 (fun ψ ↦ by
    change ‖map hN ψ‖ ≤ 1 * ‖ψ‖
    simpa only [one_mul] using map_norm_le hN ψ)

end Orbital

local instance groundScalarL2Complete (N : ℕ) (L : Length) : CompleteSpace (ScalarL2 N L) :=
  inferInstance

def GroundSupported {N : ℕ} {L : Length} (a : ℝ)
    (T : Density.Operator (ScalarL2 N L)) : Prop :=
  ∀ψ∈T.toCLM.kerᗮ,‖ψ‖=1 →
    ∃u : Jet N L,u.1=ψ ∧ IsGroundVector N L a u

def mixedOccupation {N : ℕ} (hN : 0<N) {L : Length}
    (T : Density.Operator (ScalarL2 N L)) : ℝ :=
  T.compressionTrace (Orbital.continuous hN)

def condensation_with_mixed_statement : Prop :=
  ∃ε₀ c₀ : ℝ,0<ε₀ ∧ 0<c₀ ∧
    ∀a ρ : ℝ,0<a → 0<ρ → ρ*a^3<ε₀ →
    ∀(N : ℕ→ℕ) (L : ℕ→Length) (hN : ∀k,0<N k),
      Tendsto N atTop atTop → Tendsto (fun k ↦ (L k).val) atTop atTop →
      Tendsto (fun k ↦ (N k:ℝ)/(L k).val^3) atTop (𝓝 ρ) →
      (∀Ψ : (k : ℕ)→Jet (N k) (L k),
        (∀k,IsGroundVector (N k) (L k) a (Ψ k)) →
        c₀≤liminf (fun k ↦ occupation (hN k) (Ψ k).1) atTop) ∧
      (∀T : (k : ℕ)→Density.Operator (ScalarL2 (N k) (L k)),
        (∀k,GroundSupported a (T k)) →
        c₀≤liminf (fun k ↦ mixedOccupation (hN k) (T k)) atTop)

end OAI.HardSphere

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.HardSphere.condensation_with_mixed_statement

end Problem

/- Formalization scope, from lean/docs/267.md: The formalization proves ground-state Bose–Einstein condensation in the dilute hard-sphere gas. There are absolute constants $\varepsilon_0,c_0>0$ such that, whenever the density $\rho$ and hard-sphere radius $a$ satisfy $\rho a^3<\varepsilon_0$, the condensate occupation fraction has limit inferior at least $c_0$ along every thermodynamic sequence with $N/L^3\to\rho$. The bound covers every pure ground state, every mixed state supported on the ground space, and the normalized ground-space projection. It is uniform in the gas parameter within this range and concerns ground states, without a positive-temperature assertion. -/
