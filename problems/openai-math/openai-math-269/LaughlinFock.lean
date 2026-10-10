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

- problem_id: LaughlinFock
- collection: openai-math
- question_id: openai-math:269
- source: openai-math
- source_locator: lean/ComparatorChallenges/LaughlinFock.lean#OAI.LaughlinFock.thm_fock
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the fermionic Laughlin spectral-gap conjecture for the full V1 interaction at filling 1/3 on the round sphere. The unique ground state remains uniformly gapped under sufficiently weak bounded real scalar one-body potentials projected to the lowest Landau level. Both the gap and disorder threshold are uniform over all sufficiently large particle numbers and all normalized potential profiles. ([Lean](lean/docs/269.md)) We prove that the fermionic Laughlin V1 Hamiltonian at filling 1/3 on expanding round spheres retains a unique ground state and a uniform spectral gap under sufficiently weak bounded real scalar one-body potentials projected to the lowest Landau level. With coefficient one for each pair projector and Laughlin flux $`q=3(N-1)`$, the gap and perturbation threshold are uniform for all sufficiently large particle numbers and all potential profiles of supremum norm at most one. The result uses the uniform unperturbed Fock-space gap and gives existential constants. We prove the spherical fermionic Laughlin spectral-gap conjecture for the full V1 interaction. With coefficient one for each pair projector, the gap above the Laughlin state at filling 1/3 on the round sphere is at least 1/25 for all sufficiently large systems. More generally, $`H_Q^2\ge\gamma H_Q`$ for some fixed $`\gamma\gt 1/25`$ on the entire lowest-Landau-level Fock space for all sufficiently large flux Q, independently of particle number.
- notes: OpenAI math result family 269, Uniform Laughlin gap and stability under bounded scalar disorder -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/269.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LaughlinFock.thm_fock
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.LaughlinFock.Main
- source_papers: preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf
- source_scope_note: lean/docs/269.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! The spherical V₁ Hamiltonian inequality on the full fermionic Fock space. -/

noncomputable section

namespace Laughlin

noncomputable def pairCoefficient (Q p : ℕ) (x y : Fin (Q+1)) : ℝ :=
  if x.val + y.val = p+1 then
    ((x.val : ℝ) - (y.val : ℝ)) *
      Real.sqrt (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) *
        (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) / Real.sqrt 2
  else 0

end Laughlin

run_cmd Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace LaughlinFock

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

abbrev Orbital (Q : ℕ) := Fin (Q + 1)
abbrev Occupation (Q : ℕ) := Finset (Orbital Q)
abbrev FockMatrix (Q : ℕ) := Matrix (Occupation Q) (Occupation Q) ℂ

def tensorPairCoefficient (Q p : ℕ) (i j : Orbital Q) : ℝ :=
  _root_.OAI.Laughlin.pairCoefficient Q p i j

def pairCoefficient (Q p : ℕ) (i j : Orbital Q) : ℝ :=
  Real.sqrt 2 * tensorPairCoefficient Q p i j

def annihilator (Q : ℕ) (j : Orbital Q) : FockMatrix Q := fun A B =>
  if j ∈ B ∧ A = B.erase j then
    (-1 : ℂ) ^ (B.filter (fun i => i < j)).card
  else 0

def pairAnnihilator (Q p : ℕ) : FockMatrix Q :=
  ∑ i : Orbital Q, ∑ j : Orbital Q,
    if i < j then
      (pairCoefficient Q p i j : ℂ) • (annihilator Q j * annihilator Q i)
    else 0

def hamiltonian (Q : ℕ) : FockMatrix Q :=
  ∑ p ∈ Finset.range (2 * Q - 1),
    (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p

def gammaStar : ℝ := 4616733319001 / 10 ^ 14

def FockInequality (Q : ℕ) (γ : ℝ) : Prop :=
  (hamiltonian Q * hamiltonian Q - γ • hamiltonian Q).PosSemidef

def thm_fock_statement : Prop :=
  ∀ (γ : ℝ) (hγ : 0 < γ) (hγStar : γ < gammaStar),
    ∃ Qγ : ℤ, 1 ≤ Qγ ∧ ∀ Q : ℤ, Qγ ≤ Q → FockInequality Q.toNat γ

end LaughlinFock

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LaughlinFock.thm_fock_statement

end Problem

/- Formalization scope, from lean/docs/269.md: The linked formalization proves the uniform unperturbed gap estimate used in the paper's stability argument for the fermionic Laughlin state at filling $1/3$ on the sphere. At flux $q=3(N-1)$ and all sufficiently large particle numbers $N$, every antisymmetric state has $V_1$ energy at least $1/25$ times its squared distance from the Laughlin ground-state line. This selected statement is the unperturbed Fock-space inequality. Stability under projected one-body potentials and uniqueness of the perturbed ground state are outside it. The Laughlin spectral-gap problem asks for a positive gap that remains uniform as the system grows. The formalization includes the finite spherical $V_1$ bound of $1/100$ above the Laughlin state at flux $3(N-1)$ for all sufficiently large particle numbers $N$. It also proves the stronger Fock-space inequality $H_Q^2\ge\gamma H_Q$ for every fixed $0<\gamma<\gamma_*$ and all sufficiently large fluxes $Q$, independently of particle number, where $\gamma_*=4616733319001/10^{14}>1/25$. For the untruncated planar model, the formalization proves the corresponding inequality at the endpoint $\gamma_*$ on every homogeneous particle sector. These statements use coefficient one for each pair projector. -/
