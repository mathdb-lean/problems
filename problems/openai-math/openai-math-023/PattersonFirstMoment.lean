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

- problem_id: PattersonFirstMoment
- collection: openai-math
- question_id: openai-math:023
- source: openai-math
- source_locator: lean/ComparatorChallenges/PattersonFirstMoment.lean#OAI.CubicFirstMoment.patterson_firstMoment
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves unconditionally the all-primary-prime form of Patterson’s first-moment asymptotic: normalized cubic Gauss sums over primary Eisenstein primes of norm at most X, including both conjugates, have an explicit positive main term of order $`X^{5/6}/\log X`$. Every fixed nonzero prime-angle Fourier mode has smaller order. ([Lean](lean/docs/023.md)) We prove Patterson's first-moment conjecture for normalized cubic Gauss sums over all primary Eisenstein primes, unconditionally. The sharp-cutoff main term is $`(6/5)c_*X^{5/6}/\log X`$, where $`c_*=(2\pi)^{2/3}/(3\Gamma(2/3))`$. For every fixed nonzero angular Fourier mode of the prime argument, we also prove cancellation at the first-moment scale.
- notes: OpenAI math result family 023, Patterson's first moment for cubic Gauss sums -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/023.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CubicFirstMoment.patterson_firstMoment OAI.CubicFirstMoment.patterson_angularComparison OAI.CubicFirstMoment.patterson_angularCancellation
- source_theorem_count: 3
- source_solution_module: OAI.NumberTheory.CubicMoment.Theta.CubicThetaMains
- source_papers: preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf
- source_scope_note: lean/docs/023.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Primary Eisenstein elements, residue characters, Gauss sums and first-moment target definitions. -/

section

noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def omega : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

def eisensteinRing : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {omega}
abbrev Eisenstein := eisensteinRing

def omegaE : Eisenstein :=
  ⟨omega, Algebra.subset_adjoin (Set.mem_singleton omega)⟩

def norm (a : Eisenstein) : ℝ := Complex.normSq (a : ℂ)

def normNat (a : Eisenstein) : ℕ := ⌊norm a⌋₊

def primary (a : Eisenstein) : Prop := (3 : Eisenstein) ∣ a - 1

def primaryPrime (a : Eisenstein) : Prop := primary a ∧ Prime a

def modulus (a : Eisenstein) : Ideal Eisenstein := Ideal.span {a}

abbrev Residues (a : Eisenstein) := Eisenstein ⧸ modulus a

def residueRepresentative (a : Eisenstein) (v : Residues a) : Eisenstein :=
  Classical.choose (Ideal.Quotient.mk_surjective v)

def cubicSymbolAtPrime (p v : Eisenstein) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (modulus p) v) then
    if h : ∃ j : Fin 3,
        Ideal.Quotient.mk (modulus p) (v ^ ((normNat p - 1) / 3)) =
          Ideal.Quotient.mk (modulus p) (omegaE ^ (j : ℕ)) then
      omega ^ ((Classical.choose h : Fin 3) : ℕ)
    else 0
  else 0

def additivePhase (p v : Eisenstein) : ℂ :=
  let z : ℂ := (v : ℂ) / (p : ℂ)
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z + star z))

def gaussAtPrime (p : Eisenstein) : ℂ :=
  (Real.sqrt (norm p) : ℂ)⁻¹ *
    ∑' v : Residues p,
      cubicSymbolAtPrime p (residueRepresentative p v) *
        additivePhase p (residueRepresentative p v)

def cStar : ℝ := (2 * Real.pi) ^ (2 / 3 : ℝ) / (3 * Real.Gamma (2 / 3))

def primeCutoffSum (f : Eisenstein → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Eisenstein, if primaryPrime p ∧ norm p ≤ X then f p else 0

def firstMomentScale (X : ℝ) : ℝ := X ^ (5 / 6 : ℝ) / Real.log X

def FirstMomentStatement : Prop :=
  Asymptotics.IsLittleO Filter.atTop
    (fun X : ℝ => primeCutoffSum gaussAtPrime X -
      (((6 / 5 : ℝ) * cStar * firstMomentScale X : ℝ) : ℂ))
    firstMomentScale

def theta (ℓ : ℤ) (a : Eisenstein) : ℂ := ((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) ^ ℓ

def AngularComparisonStatement : Prop :=
  ∀ ℓ : ℤ, Asymptotics.IsLittleO Filter.atTop
    (primeCutoffSum (fun p => theta ℓ p *
       (gaussAtPrime p - ((cStar * norm p ^ (-1 / 6 : ℝ) : ℝ) : ℂ))))
    firstMomentScale

def AngularCancellationStatement : Prop :=
  ∀ ℓ : ℤ, ℓ ≠ 0 → Asymptotics.IsLittleO Filter.atTop
    (primeCutoffSum (fun p => theta ℓ p * gaussAtPrime p)) firstMomentScale

/-- The sharp first moment over all primary Eisenstein primes. -/
def patterson_firstMoment_statement : Prop :=
  FirstMomentStatement

/-- Model comparison in every fixed integer angular mode. -/
def patterson_angularComparison_statement : Prop :=
  AngularComparisonStatement

/-- Cancellation at the first-moment scale for each nonzero angular mode. -/
def patterson_angularCancellation_statement : Prop :=
  AngularCancellationStatement

end CubicFirstMoment
end
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CubicFirstMoment.patterson_firstMoment_statement ∧
  _root_.OAI.CubicFirstMoment.patterson_angularComparison_statement ∧
  _root_.OAI.CubicFirstMoment.patterson_angularCancellation_statement

end Problem

/- Formalization scope, from lean/docs/023.md: Patterson's first-moment conjecture concerns the average of normalized cubic Gauss sums over primary Eisenstein primes. The formalization proves the sharp-cutoff asymptotic with main term $\frac65c_*X^{5/6}/\log X$, where $c_*=(2\pi)^{2/3}/(3\Gamma(2/3))$. It also proves the corresponding angular comparison for every integer Fourier mode and cancellation of order $o(X^{5/6}/\log X)$ for each fixed nonzero mode. All primary Eisenstein primes are included, without an extra conjectural premise. -/
