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

- problem_id: DuttaDomain
- collection: openai-math
- question_id: openai-math:194
- source: openai-math
- source_locator: lean/ComparatorChallenges/DuttaDomain.lean#OAI.Lech.dutta_domain
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves $`e(R)\le e(S)`$ for every flat local homomorphism of nonzero Noetherian local rings, where e is Hilbert–Samuel multiplicity. This resolves Lech's conjecture in every dimension and characteristic. ([Lean](lean/docs/194.md)) We prove Lech's multiplicity conjecture: Hilbert–Samuel multiplicity cannot decrease under a flat local homomorphism of nonzero Noetherian local rings. The result holds in arbitrary dimension, with no restrictions on the residue fields or characteristics.
- notes: OpenAI math result family 194, Lech’s multiplicity conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/194.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Lech.dutta_domain
- source_theorem_count: 1
- source_solution_module: OAI.RingTheory.Multiplicity.Main
- source_papers: preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/194.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
namespace Lech
noncomputable def dimension (A : Type*) [CommRing A] : ℕ :=
  (WithBot.unbotD 0 (ringKrullDim A)).toNat

noncomputable def colength (A : Type*) [CommRing A] [IsLocalRing A]
    (N : ℕ) : ℕ :=
  (Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N)).toNat

noncomputable def normalizedColength (A : Type*) [CommRing A] [IsLocalRing A]
    (N : ℕ) : ℝ :=
  (Nat.factorial (dimension A) : ℝ) * (colength A N : ℝ) /
    (N : ℝ) ^ dimension A

noncomputable def multiplicity (A : Type*) [CommRing A] [IsLocalRing A] : ℝ :=
  Filter.limUnder Filter.atTop (normalizedColength A)
end Lech


 

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

 
structure IsShortComplex (F : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  term_free : ∀ i, Module.Free R (F.X i)
  term_finite : ∀ i, Module.Finite R (F.X i)
  bounded : ∀ i, i < -(dimension R : ℤ) ∨ 0 < i → IsZero (F.X i)
  homology_finite_length : ∀ i, IsFiniteLength R (F.homology i)
  homology_zero_nonzero : ¬ IsZero (F.homology 0)

 

def frobeniusComplex (p : ℕ) [Fact p.Prime] [CharP R p] (n : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.extendScalars (iterateFrobenius R p n)).mapHomologicalComplex (.up ℤ)).obj F

 
def shortEuler (F : CochainComplex (ModuleCat.{u} R) ℤ) : ℝ :=
  ∑ i∈Finset.range (dimension R+1),(-1:ℝ)^i*
    ((Module.length R (F.homology (-(i:ℤ)))).toNat : ℝ)

def duttaSequence (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) : ℝ :=
  (p:ℝ)^(-(n*dimension R : ℤ)) * shortEuler R (frobeniusComplex R p n F)

def duttaMultiplicity (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) : ℝ :=
  limUnder atTop (duttaSequence R p F)

 

def DuttaDomainClaim : Prop :=
  ∀ (D : Type u) [CommRing D] [IsNoetherianRing D] [IsLocalRing D] [IsDomain D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    (F : CochainComplex (ModuleCat.{u} D) ℤ), IsShortComplex D F →
      (∀ n i,IsFiniteLength D ((frobeniusComplex D p n F).homology i)) ∧
      Tendsto (duttaSequence D p F) atTop (𝓝 (duttaMultiplicity D p F)) ∧
      multiplicity D ≤ duttaMultiplicity D p F
end Lech

namespace Lech
universe u
def dutta_domain_statement : Prop :=
  DuttaDomainClaim.{u}
end Lech

end
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.Lech.dutta_domain_statement.{u}

end Problem

/- Formalization scope, from lean/docs/194.md: Lech's multiplicity conjecture compares Hilbert–Samuel multiplicities across flat local maps. The linked formalization covers a supporting characteristic-$p$ comparison over a complete Noetherian local domain $D$: for a complex satisfying the stated short-complex and finite-length homology conditions, its Frobenius multiplicity sequence converges to its Dutta multiplicity, and the Hilbert–Samuel multiplicity of $D$ is at most that Dutta multiplicity. This selected statement is the complete-domain Dutta comparison. The paper's full flat-local result in arbitrary characteristic is outside it. -/
