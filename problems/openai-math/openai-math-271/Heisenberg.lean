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

- problem_id: Heisenberg
- collection: openai-math
- question_id: openai-math:271
- source: openai-math
- source_locator: lean/ComparatorChallenges/Heisenberg.lean#OAI.Heisenberg.spontaneous_magnetization
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Bloch's T3/2 law with its exact coefficient for three-dimensional quantum Heisenberg ferromagnets at every positive quantum spin, allowing nonnegative symmetric finite-range couplings whose support generates ℤ3. The thermodynamic limit precedes the zero-field derivative and low-temperature limit. The family also proves spontaneous magnetization for nearest-neighbor models in every dimension d ≥ 3 and determines the first lattice correction for three-dimensional nearest-neighbor couplings. ([Lean](lean/docs/271.md)) For every dimension d ≥ 3 and every spin $`S\in\{\frac12,1,\frac32,\ldots\}`$, we prove that the nearest-neighbor isotropic quantum Heisenberg ferromagnet has a translation-invariant, spontaneously magnetized equilibrium state at every sufficiently low positive temperature. The same state satisfies the KMS condition for the zero-field dynamics and has magnetization at least $`S/4`$. This resolves the low-temperature ordering problem in the spontaneous-magnetization formulation.
- notes: OpenAI math result family 271, Bloch's law, its lattice correction, and the spherical magnetization law -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/271.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Heisenberg.spontaneous_magnetization
- source_theorem_count: 1
- source_solution_module: OAI.MathematicalPhysics.Heisenberg.Main
- source_papers: preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf
- source_scope_note: lean/docs/271.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

universe u v


open scoped ComplexConjugate ENNReal Classical

namespace Heisenberg

abbrev L2 (ι : Type u) := lp (fun _ : ι => ℂ) 2

def l2Reindex {ι : Type u} {κ : Type v} (e : ι ≃ κ) : L2 ι ≃ₗᵢ[ℂ] L2 κ where
  toFun f := ⟨fun j => f (e.symm j), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  invFun f := ⟨fun i => f (e i), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  left_inv f := by ext i; simp
  right_inv f := by ext j; simp
  map_add' f g := by ext j; rfl
  map_smul' c f := by ext j; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun i => ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

def l2Projection {ι : Type u} (p : ι → Prop) : L2 ι →L[ℂ] L2 ι := by
  classical
  let f : L2 ι →ₗ[ℂ] L2 ι :=
    { toFun := fun v => ⟨fun i => if p i then v i else 0,
        (lp.memℓp v).mono' (fun i => by split_ifs <;> simp)⟩
      map_add' := fun v w => by
        ext i
        change (if p i then v i + w i else 0) =
          (if p i then v i else 0) + (if p i then w i else 0)
        by_cases h : p i <;> simp [h]
      map_smul' := fun c v => by ext i; by_cases h : p i <;> simp [h] }
  exact f.mkContinuous 1 (fun v => by
    simpa only [one_mul] using lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (x := f v) (y := v) (fun i => by
        change ‖if p i then v i else 0‖ ≤ ‖v i‖
        split_ifs <;> simp))

abbrev Site (d : ℕ) := Fin d → ℤ
abbrev Level (ℓ : ℕ) := Fin (ℓ + 1)
abbrev Configuration (d ℓ : ℕ) := Site d →₀ Level ℓ
abbrev SpinHilbert (d ℓ : ℕ) := L2 (Configuration d ℓ)
abbrev SpinOperator (d ℓ : ℕ) := SpinHilbert d ℓ →L[ℂ] SpinHilbert d ℓ

def configPerm (d ℓ : ℕ) (x : Site d) (σ : Equiv.Perm (Level ℓ)) :
    Equiv.Perm (Configuration d ℓ) where
  toFun c := c.update x (σ (c x))
  invFun c := c.update x (σ.symm (c x))
  left_inv c := by
    classical
    ext y
    by_cases h : y = x <;> simp [Finsupp.update_apply, h]
  right_inv c := by
    classical
    ext y
    by_cases h : y = x <;> simp [Finsupp.update_apply, h]

def matrixUnit (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) : SpinOperator d ℓ :=
  (l2Projection (fun c : Configuration d ℓ => c x = a)).comp
    (l2Reindex (configPerm d ℓ x (Equiv.swap a b))).toContinuousLinearEquiv.toContinuousLinearMap

def operatorRelabel (d ℓ : ℕ) (e : Equiv.Perm (Site d)) :
    SpinOperator d ℓ ≃⋆ₐ[ℂ] SpinOperator d ℓ :=
  (l2Reindex (Finsupp.equivCongrLeft e)).conjStarAlgEquiv

def quasiLocalAlgebra (d ℓ : ℕ) : StarSubalgebra ℂ (SpinOperator d ℓ) :=
  (StarAlgebra.adjoin ℂ {A | ∃ x a b, A = matrixUnit d ℓ x a b}).topologicalClosure

abbrev QuasiLocal (d ℓ : ℕ) := quasiLocalAlgebra d ℓ

def localUnit (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) : QuasiLocal d ℓ :=
  ⟨matrixUnit d ℓ x a b, (StarSubalgebra.le_topologicalClosure _)
    (StarAlgebra.subset_adjoin ℂ _ ⟨x, a, b, rfl⟩)⟩

def translation (d ℓ : ℕ) (x : Site d) : QuasiLocal d ℓ →⋆ₐ[ℂ] QuasiLocal d ℓ := by
  have l2Reindex_apply {ι : Type} {κ : Type} (e : ι ≃ κ) (f : L2 ι) (j : κ) :
      l2Reindex e f j = f (e.symm j) := rfl
  have l2Projection_apply {ι : Type} (p : ι → Prop) (v : L2 ι) (i : ι) :
      l2Projection p v i = if p i then v i else 0 := by classical rfl
  have matrixUnit_apply (d ℓ : ℕ) (x : Site d) (a b : Level ℓ)
      (v : SpinHilbert d ℓ) (c : Configuration d ℓ) :
      matrixUnit d ℓ x a b v c = if c x = a then v (c.update x b) else 0 := by
    simp only [matrixUnit, ContinuousLinearMap.comp_apply, l2Projection_apply]
    split_ifs with h
    · change v (c.update x ((Equiv.swap a b).symm (c x))) = v (c.update x b)
      simp [h]
    · rfl
  have l2Reindex_symm_apply {ι : Type} {κ : Type} (e : ι ≃ κ) (v : L2 κ) (i : ι) :
      (l2Reindex e).symm v i = v (e i) := rfl
  have relabel_matrixUnit (d ℓ : ℕ) (e : Equiv.Perm (Site d))
      (x : Site d) (a b : Level ℓ) :
      operatorRelabel d ℓ e (matrixUnit d ℓ x a b) = matrixUnit d ℓ (e x) a b := by
    ext v c
    simp only [operatorRelabel, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      l2Reindex_apply, matrixUnit_apply]
    change (if c (e x) = a then
      (l2Reindex (Finsupp.equivCongrLeft e)).symm v
        (((Finsupp.equivCongrLeft e).symm c).update x b) else 0) = _
    rw [l2Reindex_symm_apply]
    by_cases h : c (e x) = a
    · simp only [h, ite_eq_left]
      apply congrArg v
      ext y
      simp only [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply,
        Finsupp.update_apply]
      by_cases hy : y = e x
      · subst y; simp
      · have hy' : e.symm y ≠ x := fun hxy => hy (by simpa using congrArg e hxy)
        simp [hy, hy']
    · simp only [h, ite_false]
  have relabel_mem (d ℓ : ℕ) (e : Equiv.Perm (Site d))
      {A : SpinOperator d ℓ} (hA : A ∈ quasiLocalAlgebra d ℓ) :
      operatorRelabel d ℓ e A ∈ quasiLocalAlgebra d ℓ := by
    let f := (operatorRelabel d ℓ e).toStarAlgHom
    have h : StarAlgebra.adjoin ℂ {A | ∃ x a b, A = matrixUnit d ℓ x a b} ≤
        (quasiLocalAlgebra d ℓ).comap f := by
      apply StarAlgebra.adjoin_le
      rintro _ ⟨x, a, b, rfl⟩
      change operatorRelabel d ℓ e (matrixUnit d ℓ x a b) ∈ quasiLocalAlgebra d ℓ
      rw [relabel_matrixUnit]
      exact (localUnit d ℓ (e x) a b).property
    have hc : IsClosed ((quasiLocalAlgebra d ℓ).comap f : Set (SpinOperator d ℓ)) :=
      (StarSubalgebra.isClosed_topologicalClosure _).preimage
        (StarAlgEquiv.isometry (operatorRelabel d ℓ e)).continuous
    exact StarSubalgebra.topologicalClosure_minimal h hc hA
  exact let f := (operatorRelabel d ℓ (Equiv.addLeft x)).toStarAlgHom
    (f.comp (quasiLocalAlgebra d ℓ).subtype).codRestrict (quasiLocalAlgebra d ℓ)
      (fun A => relabel_mem d ℓ (Equiv.addLeft x) A.property)

def magneticLevel (ℓ : ℕ) (k : Level ℓ) : ℝ := (k : ℝ) - (ℓ : ℝ) / 2

def spinZ (d ℓ : ℕ) (x : Site d) : QuasiLocal d ℓ :=
  ∑ k : Level ℓ, (magneticLevel ℓ k : ℂ) • localUnit d ℓ x k k

def spinPlus (d ℓ : ℕ) (x : Site d) : QuasiLocal d ℓ :=
  ∑ k : Fin ℓ,
    (Real.sqrt ((ℓ / 2 : ℝ) * (ℓ / 2 + 1) -
      magneticLevel ℓ k.castSucc * (magneticLevel ℓ k.castSucc + 1)) : ℂ) •
      localUnit d ℓ x k.succ k.castSucc

def spinMinus (d ℓ : ℕ) (x : Site d) : QuasiLocal d ℓ := star (spinPlus d ℓ x)

def spinX (d ℓ : ℕ) (x : Site d) : QuasiLocal d ℓ :=
  (1 / 2 : ℂ) • (spinPlus d ℓ x + spinMinus d ℓ x)

def spinY (d ℓ : ℕ) (x : Site d) : QuasiLocal d ℓ :=
  (1 / (2 * Complex.I) : ℂ) • (spinPlus d ℓ x - spinMinus d ℓ x)

def NearestNeighbor {d : ℕ} (x y : Site d) : Prop :=
  ∑ i : Fin d, |x i - y i| = (1 : ℤ)

def volumeEdges {d : ℕ} (Λ : Finset (Site d)) : Finset (Site d × Site d) :=
  (Λ ×ˢ Λ).filter fun p => NearestNeighbor p.1 p.2 ∧ WellOrderingRel p.1 p.2

def hamiltonian (d ℓ : ℕ) (Λ : Finset (Site d)) : QuasiLocal d ℓ :=
  -∑ e ∈ volumeEdges Λ,
    (spinX d ℓ e.1 * spinX d ℓ e.2 + spinY d ℓ e.1 * spinY d ℓ e.2 +
      spinZ d ℓ e.1 * spinZ d ℓ e.2)

def box (d n : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) (n : ℤ)

def finiteDynamics (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ)
    (A : QuasiLocal d ℓ) : QuasiLocal d ℓ :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ) * A *
    NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ)

def dynamics (d ℓ : ℕ) (t : ℝ) (A : QuasiLocal d ℓ) : QuasiLocal d ℓ :=
  Filter.limUnder Filter.atTop (fun n : ℕ => finiteDynamics d ℓ (box d n) t A)

def DynamicsConverges (d ℓ : ℕ) : Prop :=
  ∀ (t : ℝ) (A : QuasiLocal d ℓ),
    Filter.Tendsto (fun n : ℕ => finiteDynamics d ℓ (box d n) t A)
      Filter.atTop (nhds (dynamics d ℓ t A))

structure State (d ℓ : ℕ) where
  functional : QuasiLocal d ℓ →L[ℂ] ℂ
  normalized : functional 1 = 1
  positive : ∀ A, (functional (star A * A)).im = 0 ∧
    0 ≤ (functional (star A * A)).re

def TranslationInvariant {d ℓ : ℕ} (ω : State d ℓ) : Prop :=
  ∀ (x : Site d) (A : QuasiLocal d ℓ), ω.functional (translation d ℓ x A) = ω.functional A

def IsKMS {d ℓ : ℕ} (β : ℝ) (ω : State d ℓ) : Prop :=
  0 < β ∧ ∀ A B : QuasiLocal d ℓ, ∃ F : ℂ → ℂ,
    ContinuousOn F {z | 0 ≤ z.im ∧ z.im ≤ β} ∧
    DifferentiableOn ℂ F {z | 0 < z.im ∧ z.im < β} ∧
    (∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ β → ‖F z‖ ≤ C) ∧
    (∀ t : ℝ, F t = ω.functional (A * dynamics d ℓ t B)) ∧
    (∀ t : ℝ, F ((t : ℂ) + Complex.I * β) = ω.functional (dynamics d ℓ t B * A))

open scoped Classical BigOperators ComplexConjugate
open Filter Topology

def spontaneous_magnetization_statement : Prop :=
  ∀ (d ℓ : ℕ) (hd : 3≤d) (hℓ : 1≤ℓ),
    DynamicsConverges d ℓ ∧
      ∃ β₀ : ℝ,0<β₀ ∧ ∀ β : ℝ,β₀≤β →
        ∃ ω : State d ℓ,TranslationInvariant ω ∧ IsKMS β ω ∧
          (ω.functional (spinZ d ℓ 0)).im=0 ∧
          (ℓ:ℝ)/8≤(ω.functional (spinZ d ℓ 0)).re

end Heisenberg

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Heisenberg.spontaneous_magnetization_statement

end Problem

/- Formalization scope, from lean/docs/271.md: The formalization proves spontaneous magnetization for the nearest-neighbor isotropic quantum Heisenberg ferromagnet on $\mathbb Z^d$ for every $d\ge3$ and every spin $S\in\{\tfrac12,1,\tfrac32,\ldots\}$. At every sufficiently low positive temperature, it constructs a translation-invariant equilibrium state satisfying the KMS condition for the zero-field dynamics and having magnetization at least $S/4$. It also proves convergence of the finite-volume dynamics to the infinite-volume dynamics used in the KMS statement. -/
