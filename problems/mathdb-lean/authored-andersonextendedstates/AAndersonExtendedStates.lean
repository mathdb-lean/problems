/-
Copyright 2026 The mathdb-lean Authors.

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

import FormalConjecturesUtil

/-!
Stated in this library, not converted from another corpus. Two objects Mathlib
does not construct are pinned down by their defining properties instead:
the Anderson Hamiltonian by its matrix elements in the standard basis of
`ℓ²(ℤ^d)` (a bounded operator is determined by them, and for a bounded
potential exactly one exists), and the spectral measure of a self-adjoint
operator at a vector by its moments (a finite measure with compact support is
determined by its moments, and the spectral measure is supported on the
spectrum, a compact set). The obligation asserts the existence of the
operator, so it cannot hold vacuously.

- problem_id: AAndersonExtendedStates
- collection: authored
- question_id: authored:AndersonExtendedStates
- source: mathdb-lean
- source_locator: authored/AndersonExtendedStates.lean#Target
- prose: Extended states for the Anderson model in dimension at least three. For the discrete random Schrödinger operator on ℓ²(ℤ^d) with independent uniformly distributed site potentials and small enough coupling, almost every realisation has non-empty absolutely continuous spectrum.
- notes: Anderson localization, the extended-states conjecture -- https://en.wikipedia.org/wiki/Anderson_localization
- track: open
- answer_shape: proof
- source_category: research open
- source_ams: 82 47 60
- generator: adapters/authored/adapter.py
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace Problem

/-- The lattice `ℤ^d`. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- Square-summable complex functions on `ℤ^d`, a Hilbert space. -/
noncomputable abbrev L2 (d : ℕ) := lp (fun _ : Lattice d => ℂ) 2

/-- The standard basis vector `δ_x`. -/
noncomputable def delta {d : ℕ} (x : Lattice d) : L2 d := lp.single 2 x (1 : ℂ)

/-- `IsAndersonOperator d lam ω H`: `H` is the bounded operator on `ℓ²(ℤ^d)` whose matrix in the
standard basis is the adjacency matrix of the lattice -- the discrete Laplacian without its
diagonal term, which only shifts the spectrum -- plus `lam` times the diagonal potential `ω`:
`⟨δ_x, H δ_y⟩` is `1` when `x` and `y` differ by one in exactly one coordinate, `lam * ω x` when
`x = y`, and `0` otherwise. A bounded operator is determined by these matrix elements, and for a
bounded potential exactly one such operator exists. -/
def IsAndersonOperator (d : ℕ) (lam : ℝ) (ω : Lattice d → unitInterval)
    (H : L2 d →L[ℂ] L2 d) : Prop :=
  ∀ x y : Lattice d, ⟪delta x, H (delta y)⟫_ℂ =
    if (∑ i, |x i - y i|) = 1 then 1
    else if x = y then ((lam * (ω x : ℝ) : ℝ) : ℂ) else 0

/-- `IsSpectralMeasure H ψ μ`: `μ` is the spectral measure of the self-adjoint operator `H` at
the vector `ψ`, characterised by its moments: `μ` is a finite measure on `ℝ` with compact
support and `∫ tⁿ dμ = ⟨ψ, Hⁿ ψ⟩` for every `n`. Such a measure exists (the spectral theorem)
and is unique (a compactly supported finite measure is determined by its moments). -/
def IsSpectralMeasure {d : ℕ} (H : L2 d →L[ℂ] L2 d) (ψ : L2 d) (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∧ (∃ R : ℝ, μ (Set.Icc (-R) R)ᶜ = 0) ∧
    ∀ n : ℕ, ∫ t, t ^ n ∂μ = (⟪ψ, (H ^ n) ψ⟫_ℂ).re

/-- `H` has non-empty absolutely continuous spectrum: some non-zero vector has a spectral
measure that is absolutely continuous with respect to Lebesgue measure. -/
def HasAbsolutelyContinuousSpectrum {d : ℕ} (H : L2 d →L[ℂ] L2 d) : Prop :=
  ∃ ψ : L2 d, ψ ≠ 0 ∧ ∃ μ : Measure ℝ, IsSpectralMeasure H ψ μ ∧ μ ≪ volume

/-- The random potential: independent values, uniform on `[0, 1]`, at every lattice site. -/
noncomputable def disorder (d : ℕ) : Measure (Lattice d → unitInterval) :=
  Measure.infinitePi fun _ => (volume : Measure unitInterval)

/-- The extended-states conjecture for the Anderson model in dimension `d ≥ 3`: at weak enough
disorder, almost every realisation of the potential gives a Hamiltonian with non-empty
absolutely continuous spectrum. -/
abbrev Target : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
    ∀ᵐ ω ∂(disorder d), ∃ H : L2 d →L[ℂ] L2 d,
      IsSelfAdjoint H ∧ IsAndersonOperator d lam ω H ∧ HasAbsolutelyContinuousSpectrum H

end Problem

/-!
- source_version: b80da422c1869ddababb2992c7dc83556e0f930c
-/
