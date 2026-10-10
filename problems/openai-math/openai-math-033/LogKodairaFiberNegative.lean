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

- problem_id: LogKodairaFiberNegative
- collection: openai-math
- question_id: openai-math:033
- source: openai-math
- source_locator: lean/ComparatorChallenges/LogKodairaFiberNegative.lean#OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Campana's orbifold Iitaka subadditivity conjecture for smooth Fujiki-class-$`\mathcal C`$ manifolds with rational simple-normal-crossing boundaries. For projective fibrations $`f:U\to V`$ of smooth complex quasi-projective varieties with connected fibers, general fiber F, and $`\bar\kappa(V)\ge0`$, proves Popa's inequality $`\bar\kappa(U)\ge\kappa(F)+\max\{\bar\kappa(V),\mathop{\mathrm{Var}}\nolimits (f)\}`$, where variation measures the whole geometric generic fiber. ([Lean](lean/docs/033.md)) We prove the reverse logarithmic Kodaira inequality for a surjective connected-fiber morphism $`f:(X,E)\to(Y,D)`$ of smooth projective reduced simple-normal-crossing pairs, with $`\mathop{\mathrm{Supp}}\nolimits (f^*D)\subseteq\mathop{\mathrm{Supp}}\nolimits E`$, such that X and every boundary stratum are smooth over $`Y\setminus\mathop{\mathrm{Supp}}\nolimits D`$. Together with logarithmic subadditivity, the inequality gives additivity, including both negative-infinity cases. This resolves Popa's logarithmic additivity conjecture positively in the projective reduced-SNC, stratum-smooth setting.
- notes: OpenAI math result family 033, Iitaka subadditivity, variation, and logarithmic additivity -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/033.md
- track: solved
- answer_shape: proof
- context_lemmas: germ_constants isLogPluriform_zero isLogPluriform_add isLogPluriform_smul
- source_theorem: OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch
- source_theorem_count: 1
- source_solution_module: OAI.AlgebraicGeometry.LogKodaira.FiberNegative
- source_papers: preprints/The-reverse-logarithmic-Kodaira-inequality-and-additivity-September-26-2026/paper.pdf
- source_scope_note: lean/docs/033.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

 

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev complexBase : Scheme := Spec (CommRingCat.of ℂ)

abbrev projectiveGrading (N : ℕ) := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ

abbrev complexProjectiveSpace (N : ℕ) : Scheme := Proj (projectiveGrading N)

def projectiveConstants (N : ℕ) : ℂ →+* projectiveGrading N 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin (N + 1)) r⟩
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_add' x y := Subtype.ext (map_add MvPolynomial.C x y)
  map_mul' x y := Subtype.ext (map_mul MvPolynomial.C x y)

def complexProjectiveStructure (N : ℕ) : complexProjectiveSpace N ⟶ complexBase :=
  Proj.toSpecZero (projectiveGrading N) ≫ Spec.map (CommRingCat.ofHom (projectiveConstants N))

 
structure SmoothProjectiveVariety where
  scheme : Scheme
  structural : scheme ⟶ complexBase
  dimension : ℕ
  integral : IsIntegral scheme
  smooth : SmoothOfRelativeDimension dimension structural
  projective : ∃ (N : ℕ) (i : scheme ⟶ complexProjectiveSpace N),
    IsClosedImmersion i ∧ i ≫ complexProjectiveStructure N = structural

attribute [instance] SmoothProjectiveVariety.integral SmoothProjectiveVariety.smooth

namespace SmoothProjectiveVariety

instance (X : SmoothProjectiveVariety) : Smooth X.structural :=
  SmoothOfRelativeDimension.smooth X.dimension X.structural

 
def globalConstants (X : SmoothProjectiveVariety) : ℂ →+* Γ(X.scheme, ⊤) :=
  X.structural.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

 
def constants (X : SmoothProjectiveVariety) (U : X.scheme.Opens) : ℂ →+* Γ(X.scheme, U) :=
  (X.scheme.presheaf.map (homOfLE (le_top (a := U))).op).hom.comp X.globalConstants

instance (X : SmoothProjectiveVariety) (U : X.scheme.Opens) : Algebra ℂ Γ(X.scheme, U) :=
  (X.constants U).toAlgebra

instance (X : SmoothProjectiveVariety) : Nonempty (⊤ : X.scheme.Opens) :=
  ⟨⟨genericPoint X.scheme, by trivial⟩⟩

 
def functionFieldConstants (X : SmoothProjectiveVariety) : ℂ →+* X.scheme.functionField :=
  (X.scheme.germToFunctionField ⊤).hom.comp X.globalConstants

instance (X : SmoothProjectiveVariety) : Algebra ℂ X.scheme.functionField :=
  X.functionFieldConstants.toAlgebra

lemma germ_constants (X : SmoothProjectiveVariety) (U : X.scheme.Opens) [Nonempty U] (c : ℂ) :
    algebraMap Γ(X.scheme, U) X.scheme.functionField (algebraMap ℂ Γ(X.scheme, U) c) =
      algebraMap ℂ X.scheme.functionField c := by
  change X.scheme.presheaf.germ U (genericPoint X.scheme) _
    (X.scheme.presheaf.map (homOfLE (le_top (a := U))).op (X.globalConstants c)) =
      X.scheme.presheaf.germ ⊤ (genericPoint X.scheme) _ (X.globalConstants c)
  exact X.scheme.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X.scheme) _ _

instance (X : SmoothProjectiveVariety) (U : X.scheme.Opens) [Nonempty U] :
    IsScalarTower ℂ Γ(X.scheme, U) X.scheme.functionField :=
  IsScalarTower.of_algebraMap_eq fun c => (X.germ_constants U c).symm

abbrev RationalCanonical (X : SmoothProjectiveVariety) :=
  ⋀[X.scheme.functionField]^X.dimension (KaehlerDifferential ℂ X.scheme.functionField)

abbrev RationalPluriform (X : SmoothProjectiveVariety) (m : ℕ) :=
  ⨂[X.scheme.functionField]^m X.RationalCanonical

instance (X : SmoothProjectiveVariety) (m : ℕ) : AddCommGroup (X.RationalPluriform m) :=
  Module.addCommMonoidToAddCommGroup X.scheme.functionField

def regularPluriformLattice (X : SmoothProjectiveVariety) (U : X.scheme.affineOpens)
    [Nonempty U.1] (m : ℕ) : Submodule Γ(X.scheme, U.1) (X.RationalPluriform m) :=
  Submodule.span Γ(X.scheme, U.1) <| Set.range fun a : Fin m → Fin X.dimension → Γ(X.scheme, U.1) =>
    PiTensorProduct.tprod X.scheme.functionField fun j =>
      exteriorPower.ιMulti X.scheme.functionField X.dimension fun i =>
        KaehlerDifferential.D ℂ X.scheme.functionField (algebraMap _ _ (a j i))

 

def IsCartierIdeal (X : SmoothProjectiveVariety) (I : X.scheme.IdealSheafData) : Prop :=
  ∀ x : X.scheme, ∃ (U : X.scheme.affineOpens), x ∈ U.1 ∧
    ∃ t : Γ(X.scheme, U.1), t ≠ 0 ∧ I.ideal U = Ideal.span {t}

structure ReducedSNCBoundary (X : SmoothProjectiveVariety) where
  count : ℕ
  components : Fin count → X.scheme.IdealSheafData
  cartier : ∀ i, X.IsCartierIdeal (components i)
  transverse : ∀ S : Finset (Fin count), S.Nonempty →
    IsEmpty ((S.sup components).subscheme) ∨
      (S.card ≤ X.dimension ∧ SmoothOfRelativeDimension (X.dimension - S.card)
        ((S.sup components).subschemeι ≫ X.structural))
  union_cartier : X.IsCartierIdeal (∏ i, components i)

namespace ReducedSNCBoundary

def ideal {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) : X.scheme.IdealSheafData :=
  ∏ i, E.components i

 
def support {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) : Set X.scheme :=
  E.ideal.support

def IsLogPluriform {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary)
    (m : ℕ) (s : X.RationalPluriform m) : Prop :=
  ∀ (U : X.scheme.affineOpens) (_ : Nonempty U.1) (t : Γ(X.scheme, U.1)),
    t ≠ 0 → E.ideal.ideal U = Ideal.span {t} →
      (algebraMap Γ(X.scheme, U.1) X.scheme.functionField t)^m • s ∈
        X.regularPluriformLattice U m

lemma isLogPluriform_zero {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) (m : ℕ) :
    E.IsLogPluriform m 0 := by
  intro U hU t ht hI
  simp only [smul_zero, Submodule.zero_mem]

lemma isLogPluriform_add {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) (m : ℕ)
    {s r : X.RationalPluriform m} (hs : E.IsLogPluriform m s) (hr : E.IsLogPluriform m r) :
    E.IsLogPluriform m (s + r) := by
  intro U hU t ht hI
  simpa only [smul_add] using (X.regularPluriformLattice U m).add_mem
    (hs U hU t ht hI) (hr U hU t ht hI)

lemma isLogPluriform_smul {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) (m : ℕ)
    (c : ℂ) {s : X.RationalPluriform m} (hs : E.IsLogPluriform m s) :
    E.IsLogPluriform m (c • s) := by
  intro U hU t ht hI
  have h := (X.regularPluriformLattice U m).smul_mem
    (algebraMap ℂ Γ(X.scheme, U.1) c) (hs U hU t ht hI)
  rw [IsScalarTower.algebraMap_smul Γ(X.scheme, U.1)] at h
  rwa [smul_comm c] at h

 

def sections {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) (m : ℕ) :
    Submodule ℂ (X.RationalPluriform m) where
  carrier := E.IsLogPluriform m
  zero_mem' := E.isLogPluriform_zero m
  add_mem' := E.isLogPluriform_add m
  smul_mem' := E.isLogPluriform_smul m

 

def HasImageDimensionAtLeast {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) (k : ℕ) : Prop :=
  ∃ (m : ℕ), 0 < m ∧ ∃ s : X.RationalPluriform m,
    s ∈ E.sections m ∧ s ≠ 0 ∧ ∃ r : Fin k → X.scheme.functionField,
      AlgebraicIndependent ℂ r ∧ ∀ i, r i • s ∈ E.sections m

 

def kodaira {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) : WithBot ℕ∞ :=
  ⨆ (k : ℕ) (_ : E.HasImageDimensionAtLeast k), ((k : ℕ∞) : WithBot ℕ∞)

end ReducedSNCBoundary

 
structure ComplexPoint (X : SmoothProjectiveVariety) where
  hom : complexBase ⟶ X.scheme
  over_base : hom ≫ X.structural = 𝟙 complexBase

 
def complexBasePoint : complexBase := ⟨⊥, Ideal.isPrime_bot⟩

 
def ComplexPoint.point {X : SmoothProjectiveVariety} (y : X.ComplexPoint) : X.scheme :=
  y.hom complexBasePoint

 
def ReducedSNCBoundary.complement {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary) :
    X.scheme.Opens := E.ideal.support.compl

 

structure BoundaryFibration (X Y : SmoothProjectiveVariety)
    (E : X.ReducedSNCBoundary) (D : Y.ReducedSNCBoundary) where
  hom : X.scheme ⟶ Y.scheme
  over_base : hom ≫ Y.structural = X.structural
  surjective : Surjective hom
  connected : ∀ y : Y.ComplexPoint, ConnectedSpace ↥(CategoryTheory.Limits.pullback hom y.hom)
  support : hom ⁻¹' D.support ⊆ E.support

 

structure StratumSmoothFibration (X Y : SmoothProjectiveVariety)
    (E : X.ReducedSNCBoundary) (D : Y.ReducedSNCBoundary)
    extends BoundaryFibration X Y E D where
  smooth : Smooth (hom.resLE D.complement (hom ⁻¹ᵁ D.complement) le_rfl)
  strata : ∀ (S : Finset (Fin E.count)), S.Nonempty →
    Smooth (((S.sup E.components).subschemeι ≫ hom).resLE D.complement
      (((S.sup E.components).subschemeι ≫ hom) ⁻¹ᵁ D.complement) le_rfl)

 

structure FiberModel {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary}
    {D : Y.ReducedSNCBoundary} (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) where
  variety : SmoothProjectiveVariety
  inclusion : variety.scheme ⟶ X.scheme
  square : IsPullback inclusion variety.structural f.hom y.hom
  boundary : variety.ReducedSNCBoundary
  boundary_pullback : boundary.ideal = E.ideal.comap inclusion

 

def VeryGenerally (Y : SmoothProjectiveVariety) (P : Y.ComplexPoint → Prop) : Prop :=
  ∃ Z : ℕ → TopologicalSpace.Closeds Y.scheme,
    (∀ n, Z n ≠ ⊤) ∧ ∀ y : Y.ComplexPoint, (∀ n, y.point ∉ Z n) → P y

end SmoothProjectiveVariety

end ReverseLogKodaira

namespace ReverseLogKodaira.SmoothProjectiveVariety

def veryGenerally_fiber_negative_branch_statement : Prop :=
  ∀ {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary} (f : StratumSmoothFibration X Y E D),
    VeryGenerally Y fun y => y.point ∈ D.complement ∧
      ∀ F : FiberModel f.toBoundaryFibration y, F.boundary.kodaira = ⊥ →
        E.kodaira = D.kodaira + F.boundary.kodaira ∧
        ∀ (m : ℕ), 0 < m → ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0

end ReverseLogKodaira.SmoothProjectiveVariety

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch_statement

end Problem

/- Formalization scope, from lean/docs/033.md: The paper studies logarithmic Kodaira additivity for connected-fiber morphisms of smooth projective reduced simple-normal-crossing pairs that are smooth on all boundary strata away from the base boundary. The linked formalization proves the negative-fiber branch: for a very general base point, if the logarithmic Kodaira dimension of the fiber is $-\infty$, then the total logarithmic Kodaira dimension equals the sum of the base and fiber dimensions and is $-\infty$. Every positive-degree logarithmic pluriform section on the total space then vanishes. The finite-dimension and negative-base branches of the paper's additivity theorem are outside this selected statement. -/
