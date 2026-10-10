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

- problem_id: BogomolovPopInjectivity
- collection: openai-math
- question_id: openai-math:009
- source: openai-math
- source_locator: lean/ComparatorChallenges/BogomolovPopInjectivity.lean#OAI.BogomolovPop.main_graph_injective
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Reconstructs function fields of transcendence degree at least two over algebraically closed constants from $`K^{\mathrm M}_1/\ell`$, $`K^{\mathrm M}_2/\ell`$, and their product. These data recover the perfect closure and constants when ℓ differs from the characteristic, and the original field and its named base in equal characteristic. Also proves Bogomolov–Pop reconstruction from abelian-by-central pro-ℓ Galois data away from the characteristic. ([Lean](lean/docs/009.md)) We prove the Bogomolov–Pop reconstruction conjecture for function fields of transcendence degree at least two over arbitrary algebraically closed fields of characteristic different from ℓ. The pro-ℓ abelian-by-central datum determines the perfect closure and its constant field, with precisely the Frobenius and ℓ-adic unit ambiguities.
- notes: OpenAI math result family 009, Function-field reconstruction from Milnor K-theory and Galois data -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/009.md
- track: solved
- answer_shape: proof
- context_lemmas: closedGammaThree_le abelianLift_spec
- source_theorem: OAI.BogomolovPop.main_graph_injective
- source_theorem_count: 1
- source_solution_module: OAI.Algebra.BogomolovPop.Injectivity
- source_papers: preprints/The-Bogomolov-Pop-reconstruction-theorem-September-23-2026/paper.pdf
- source_scope_note: lean/docs/009.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
namespace BogomolovPop

def proEllKernel (ell : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Subgroup G :=
  ⨅ (H : OpenNormalSubgroup G) (_ : IsPGroup ell (G ⧸ H.toSubgroup)), H.toSubgroup

instance proEllKernel_normal (ell : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :
    (proEllKernel ell G).Normal := by
  unfold proEllKernel
  exact Subgroup.normal_iInf_normal fun H =>
    Subgroup.normal_iInf_normal fun _ => H.isNormal'

abbrev ProEll (ell : ℕ) (F : Type*) [Field F] :=
  Field.absoluteGaloisGroup F ⧸ proEllKernel ell (Field.absoluteGaloisGroup F)

def closedGammaThree (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Subgroup G :=
  (⁅(commutator G).topologicalClosure, (⊤ : Subgroup G)⁆).topologicalClosure

instance closedGammaThree_normal (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (closedGammaThree G).Normal := by
  unfold closedGammaThree
  exact Subgroup.is_normal_topologicalClosure _

abbrev PiA (ell : ℕ) (F : Type*) [Field F] := TopologicalAbelianization (ProEll ell F)

abbrev PiC (ell : ℕ) (F : Type*) [Field F] := ProEll ell F ⧸ closedGammaThree (ProEll ell F)

theorem closedGammaThree_le (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : closedGammaThree G ≤ (commutator G).topologicalClosure := by
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.commutator_le_left _ _)
    (Subgroup.isClosed_topologicalClosure _)

def centralProjection (ell : ℕ) (F : Type*) [Field F] : PiC ell F →* PiA ell F :=
  QuotientGroup.map _ _ (MonoidHom.id _) (closedGammaThree_le _)

abbrev Delta (ell : ℕ) (F : Type*) [Field F] := (centralProjection ell F).ker

def sourceCommutator {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

def abelianLift (ell : ℕ) (F : Type*) [Field F] (x : PiA ell F) : ProEll ell F :=
  Quotient.out x

theorem abelianLift_spec (ell : ℕ) (F : Type*) [Field F] (x : PiA ell F) :
    QuotientGroup.mk' _ (abelianLift ell F x) = x := Quotient.out_eq x

def bracket (ell : ℕ) (F : Type*) [Field F] (x y : PiA ell F) : Delta ell F :=
  ⟨QuotientGroup.mk' _ (sourceCommutator (abelianLift ell F x) (abelianLift ell F y)), by
    change centralProjection ell F _ = 1
    simp only [centralProjection, sourceCommutator, map_mul, map_inv]
    simp [mul_comm]⟩

def BracketCompatible {ell : ℕ} {K L : Type*} [Field K] [Field L]
    (φ : PiA ell L ≃ₜ* PiA ell K) : Prop :=
  ∃ ψ : Delta ell L ≃ₜ* Delta ell K,
    ∀ σ τ, ψ (bracket ell L σ τ) = bracket ell K (φ σ) (φ τ)

abbrev PerfectFieldClosure (F : Type*) [Field F] := perfectClosure F (AlgebraicClosure F)

def PerfectIsom (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] :=
  { α : PerfectFieldClosure K ≃+* PerfectFieldClosure L //
    α '' Set.range (algebraMap k (PerfectFieldClosure K)) =
      Set.range (algebraMap l (PerfectFieldClosure L)) }

def FrobeniusStep {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] (α β : PerfectIsom k K l L) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p : L) = 0 ∧
    ∀ x : PerfectFieldClosure K, β.1 x = (α.1 x) ^ p

abbrev IsomF (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] :=
  Quotient (Relation.EqvGen.setoid (FrobeniusStep (k := k) (K := K) (l := l) (L := L)))

abbrev IsomC (ell : ℕ) (K L : Type*) [Field K] [Field L] :=
  {φ : PiA ell L ≃ₜ* PiA ell K // BracketCompatible φ}

def ScalarStep {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L]
    (φ χ : IsomC ell K L) : Prop :=
  ∃ u : (PadicInt ell)ˣ, ∀ x : PiA ell L,
    Filter.Tendsto (fun n : ℕ => (φ.1 x) ^ PadicInt.appr (u : PadicInt ell) n)
      Filter.atTop (nhds (χ.1 x))

abbrev IsomCUnits (ell : ℕ) [Fact ell.Prime] (K L : Type*) [Field K] [Field L] :=
  Quotient (Relation.EqvGen.setoid (ScalarStep (ell := ell) (K := K) (L := L)))

def absoluteToPiA (ell : ℕ) (F : Type*) [Field F] :
    Field.absoluteGaloisGroup F →* PiA ell F :=
  (QuotientGroup.mk' _).comp (QuotientGroup.mk' _)

def absoluteAction {F : Type*} [Field F] (σ : Field.absoluteGaloisGroup F)
    (x : AlgebraicClosure F) : AlgebraicClosure F := by
  change AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F at σ
  exact σ x

def PullbackGraph {ell : ℕ} {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) (φ : IsomC ell K L) : Prop :=
  ∃ β : AlgebraicClosure K ≃+* AlgebraicClosure L,
    (∀ x : PerfectFieldClosure K, β x = ((α.1 x : PerfectFieldClosure L) :
      AlgebraicClosure L)) ∧
    ∀ σ : Field.absoluteGaloisGroup L, ∃ τ : Field.absoluteGaloisGroup K,
      (∀ x : AlgebraicClosure K,
        β (absoluteAction τ x) = absoluteAction σ (β x)) ∧
      φ.1 (absoluteToPiA ell L σ) = absoluteToPiA ell K τ

def PhiGraph {ell : ℕ} [Fact ell.Prime] {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (a : IsomF k K l L) (b : IsomCUnits ell K L) : Prop :=
  ∃ α : PerfectIsom k K l L, ∃ φ : IsomC ell K L,
    Quotient.mk _ α = a ∧ Quotient.mk _ φ = b ∧ PullbackGraph α φ

def main_graph_injective_statement : Prop :=
  ∀ (ell : ℕ) [Fact ell.Prime] (k K l L : Type*) [Field k] [Field K] [Field l] [Field L] [IsAlgClosed k] [IsAlgClosed l] [Algebra k K] [Algebra l L] [Algebra.EssFiniteType k K] [Algebra.EssFiniteType l L] (hk : (ell : k) ≠ 0) (hl : (ell : l) ≠ 0) (hK : 2 ≤ Algebra.trdeg k K) (hL : 2 ≤ Algebra.trdeg l L),
    ∀ (a a' : IsomF k K l L) (b : IsomCUnits ell K L),
      PhiGraph a b → PhiGraph a' b → a = a'

end BogomolovPop

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1, u_2, u_3, u_4} : Prop :=
  _root_.OAI.BogomolovPop.main_graph_injective_statement.{u_1, u_2, u_3, u_4}

end Problem

/- Formalization scope, from lean/docs/009.md: The Bogomolov–Pop reconstruction conjecture concerns recovering a function field and its constants from pro-$\ell$ abelian-by-central Galois data. The linked formalization proves injectivity of the reconstruction correspondence for function fields of transcendence degree at least two over algebraically closed fields of characteristic different from the prime $\ell$. If two isomorphisms of perfect closures preserving the constant fields induce the same Galois-data isomorphism modulo $\ell$-adic unit scaling, then they agree modulo Frobenius. The selected statement proves this uniqueness; existence of a field isomorphism for every admissible Galois-data isomorphism is outside it. -/
