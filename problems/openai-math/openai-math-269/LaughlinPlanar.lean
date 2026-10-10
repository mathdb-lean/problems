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

- problem_id: LaughlinPlanar
- collection: openai-math
- question_id: openai-math:269
- source: openai-math
- source_locator: lean/ComparatorChallenges/LaughlinPlanar.lean#OAI.Laughlin.planar_gap
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the fermionic Laughlin spectral-gap conjecture for the full V1 interaction at filling 1/3 on the round sphere. The unique ground state remains uniformly gapped under sufficiently weak bounded real scalar one-body potentials projected to the lowest Landau level. Both the gap and disorder threshold are uniform over all sufficiently large particle numbers and all normalized potential profiles. ([Lean](lean/docs/269.md)) We prove that the fermionic Laughlin V1 Hamiltonian at filling 1/3 on expanding round spheres retains a unique ground state and a uniform spectral gap under sufficiently weak bounded real scalar one-body potentials projected to the lowest Landau level. With coefficient one for each pair projector and Laughlin flux $`q=3(N-1)`$, the gap and perturbation threshold are uniform for all sufficiently large particle numbers and all potential profiles of supremum norm at most one. The result uses the uniform unperturbed Fock-space gap and gives existential constants. We prove the spherical fermionic Laughlin spectral-gap conjecture for the full V1 interaction. With coefficient one for each pair projector, the gap above the Laughlin state at filling 1/3 on the round sphere is at least 1/25 for all sufficiently large systems. More generally, $`H_Q^2\ge\gamma H_Q`$ for some fixed $`\gamma\gt 1/25`$ on the entire lowest-Landau-level Fock space for all sufficiently large flux Q, independently of particle number.
- notes: OpenAI math result family 269, Uniform Laughlin gap and stability under bounded scalar disorder -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/269.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Laughlin.planar_gap
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Laughlin.UniformGap
- source_papers: preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf
- source_scope_note: lean/docs/269.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Laughlin
open scoped BigOperators Matrix ENNReal

noncomputable def gammaStar : ℝ := 4616733319001 / 10^14

noncomputable def pairLimitCoefficient (p x y : ℕ) : ℝ :=
  if x+y = p+1 then
    ((x : ℝ)-(y : ℝ)) * Real.sqrt ((p.factorial : ℝ) /
      (((2 : ℕ) : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ))) / Real.sqrt (2 : ℕ)
  else 0

namespace Fock

abbrev Orbital (Q : ℕ) := Fin (Q+1) → ℂ
abbrev Space (Q : ℕ) := ExteriorAlgebra ℂ (Orbital Q)

noncomputable def annihilate {Q : ℕ} (i : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i)

noncomputable def occupationBasis (Q : ℕ) :
    Module.Basis (Finset (Fin (Q+1))) ℂ (Space Q) :=
  (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra

def OccupationBidegree (Q n w : ℕ) (x : Space Q) : Prop :=
  ∀ A : Finset (Fin (Q+1)), (A.card ≠ n ∨ (∑ i ∈ A, i.val) ≠ w) →
    (occupationBasis Q).repr x A = 0

end Fock

namespace Planar
open Fock

abbrev Occupations (L : ℕ) := Finset (Fin (L+1))

noncomputable def pairMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    Matrix (Occupations L) (Occupations L) ℂ := fun A B =>
  ∑ i, ∑ j, c i j * (occupationBasis L).repr
    (annihilate j (annihilate i (occupationBasis L B))) A

noncomputable def planarCoefficient (p i j : ℕ) : ℂ :=
  ((pairLimitCoefficient p i j / Real.sqrt (2 : ℕ) : ℝ) : ℂ)

noncomputable def planarPairMatrix (L p : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  pairMatrix L (fun i j => planarCoefficient p i.val j.val)

noncomputable def planarHamiltonian (L : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  ∑ p ∈ Finset.range (2*L+1), (planarPairMatrix L p)ᴴ * planarPairMatrix L p

noncomputable def pairEnergy (L : ℕ)
    (P : ℕ → Matrix (Occupations L) (Occupations L) ℂ) (x : Occupations L → ℂ) : ℝ :=
  ∑ p ∈ Finset.range (2*L+1), ∑ A, ‖(P p *ᵥ x) A‖^2

noncomputable def squareNorm (L : ℕ) (H : Matrix (Occupations L) (Occupations L) ℂ)
    (x : Occupations L → ℂ) : ℝ := ∑ A, ‖(H *ᵥ x) A‖^2

/-- Occupation coefficients with fixed particle number in every homogeneous degree. -/
structure HomogeneousState (N : ℕ) where
  block : (L : ℕ) → Space L
  homogeneous : ∀ L, OccupationBidegree L N L (block L)

noncomputable def fullEnergy {N : ℕ} (ψ : HomogeneousState N) : ℝ≥0∞ :=
  ∑' L, ENNReal.ofReal (pairEnergy L (planarPairMatrix L)
    (fun A => (occupationBasis L).repr (ψ.block L) A))

noncomputable def fullSquareNorm {N : ℕ} (ψ : HomogeneousState N) : ℝ≥0∞ :=
  ∑' L, ENNReal.ofReal (squareNorm L (planarHamiltonian L)
    (fun A => (occupationBasis L).repr (ψ.block L) A))

end Planar

/-- The planar endpoint inequality in the homogeneous occupation representation. -/
def planar_gap_statement : Prop :=
  ∀ {N : ℕ} (ψ : Planar.HomogeneousState N),
    ENNReal.ofReal gammaStar * Planar.fullEnergy ψ ≤ Planar.fullSquareNorm ψ

end Laughlin

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Laughlin.planar_gap_statement

end Problem

/- Formalization scope, from lean/docs/269.md: The linked formalization proves the uniform unperturbed gap estimate used in the paper's stability argument for the fermionic Laughlin state at filling $1/3$ on the sphere. At flux $q=3(N-1)$ and all sufficiently large particle numbers $N$, every antisymmetric state has $V_1$ energy at least $1/25$ times its squared distance from the Laughlin ground-state line. This selected statement is the unperturbed Fock-space inequality. Stability under projected one-body potentials and uniqueness of the perturbed ground state are outside it. The Laughlin spectral-gap problem asks for a positive gap that remains uniform as the system grows. The formalization includes the finite spherical $V_1$ bound of $1/100$ above the Laughlin state at flux $3(N-1)$ for all sufficiently large particle numbers $N$. It also proves the stronger Fock-space inequality $H_Q^2\ge\gamma H_Q$ for every fixed $0<\gamma<\gamma_*$ and all sufficiently large fluxes $Q$, independently of particle number, where $\gamma_*=4616733319001/10^{14}>1/25$. For the untruncated planar model, the formalization proves the corresponding inequality at the endpoint $\gamma_*$ on every homogeneous particle sector. These statements use coefficient one for each pair projector. -/
