import MathDBUtil

/-
Copyright 2026 The Formal Conjectures Authors.

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
/-
The copied Mathlib source carries the following attribution:
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/



/-!
# Restriction maps of absolute Galois groups

These definitions were introduced in Mathlib by Thomas Browning's
[pull request #41415](https://github.com/leanprover-community/mathlib4/pull/41415).
They are absent from this repository's Mathlib `v4.33.1` dependency. The added code is copied
verbatim from `Mathlib.FieldTheory.AbsoluteGaloisGroup` at the merged commit
`7e604dbff1442ed4b05a0b9a4b15c5207584f116`.
-/

noncomputable section

namespace Field

variable (K L : Type*) [Field K] [Field L]

local notation "G_K" => absoluteGaloisGroup

section

variable [Algebra K L] [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

open IntermediateField in
/-- A commuting square of two fields and their algebraic closures induces a continuous homomorphism
of their absolute Galois groups. -/
@[simps!]
noncomputable def absoluteGaloisGroup.mapOfAlgebra : G_K L →ₜ* G_K K :=
  letI F : G_K L →* G_K K := (AlgEquiv.restrictNormalHom _).comp (AlgEquiv.restrictScalarsHom K)
  { __ := F
    continuous_toFun := by
      classical
      let f := IsScalarTower.toAlgHom K (AlgebraicClosure K) (AlgebraicClosure L)
      apply continuous_of_continuousAt_one F
      rw [ContinuousAt, map_one]
      refine ((galGroupBasis L (AlgebraicClosure L)).nhds_one_hasBasis.tendsto_iff
        (galGroupBasis K (AlgebraicClosure K)).nhds_one_hasBasis).mpr ?_
      rintro _ ⟨_, ⟨F, hF : FiniteDimensional _ _, rfl⟩, rfl⟩
      refine ⟨_, ⟨_, ⟨adjoin L (F.map f), ?_, rfl⟩, rfl⟩, fun σ hσ x ↦ ?_⟩
      · suffices Algebra.EssFiniteType L (adjoin L (F.map f : Set (AlgebraicClosure L))) by
          apply Algebra.finite_of_essFiniteType_of_isAlgebraic
        replace hF : Algebra.EssFiniteType K F := inferInstance
        rw [essFiniteType_iff] at hF ⊢
        obtain ⟨s, rfl⟩ := hF
        use s.image f
        rw [adjoin_map, adjoin_adjoin_right, Finset.coe_image]
      · exact f.injective <| ((σ.restrictScalarsHom K).restrictNormal_commutes
          (AlgebraicClosure K) x).trans <| hσ ⟨f x, subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩ }

end

variable {K L} in
/-- An embedding of fields induces a continuous homomorphism of absolute Galois groups.
Note that this depends on an arbitrary choice of embedding of the algebraic closures. -/
@[simps!]
noncomputable def absoluteGaloisGroup.map (f : K →+* L) : G_K L →ₜ* G_K K :=
  letI : Algebra K L := f.toAlgebra
  letI g : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := g.toAlgebra
  absoluteGaloisGroup.mapOfAlgebra K L

end Field

end

/-
Copyright 2026 The Formal Conjectures Authors.

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
/-
The copied Mathlib source carries the following attribution:
Copyright (c) 2026 Edison Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, David Kurniadi Angdinata
-/





/-!
# The Tate–Shafarevich group of a Galois module

This file defines a general notion of a *Tate–Shafarevich group* of a Galois module (i.e. an abelian
group `A` equipped with a continuous action of the absolute Galois group `G_K` of a field `K`), as
the intersection of the kernels of the maps `Hⁿ(G_K, A) → Hⁿ(G_Kᵥ, A)`, induced by the map
`G_Kᵥ → G_K`, where `Kᵥ` is a field extension of `K` for each `v` in an arbitrary indexing set `V`.

These definitions were introduced in Mathlib by Edison Xie and David Kurniadi Angdinata's
[pull request #43529](https://github.com/leanprover-community/mathlib4/pull/43529).
They are absent from this repository's Mathlib `v4.33.1` dependency. The added code is copied
verbatim from `Mathlib.RepresentationTheory.Homological.ContCohomology.Sha` at commit
`a4c43ae1f99cb19aabfa62308b3ea75a340e470f`, except that `Mathlib.FieldTheory.AbsoluteGaloisGroup`
is replaced by this repository's copy, which supplies `Field.absoluteGaloisGroup.map`.

## Main definitions

* `ContinuousCohomology.tateShafarevich`: the Tate–Shafarevich group of a Galois module.

## TODOs

* Add a notation for `ContinuousCohomology.tateShafarevich`.
* Prove that `ContinuousCohomology.tateShafarevich` of a discrete Galois module is torsion.
* Define the classical Tate–Shafarevich group in `Mathlib/AlgebraicGeometry/EllipticCurve`.

## Implementation notes

Mathematicians seem to use "Tate–Shafarevich group" in at least three distinct contexts. They have
in common the set-up that `K` is a global field, `A` is a discrete `G_K`-module, `V` is the set of
places of `K`, and `Kᵥ` is the completion of `K` at a place `v` in `V`.

The first context is when `A` is finite. This is used, for example, in the statement of global
Poitou-Tate duality. In this theorem, the Tate–Shafarevich group is defined exactly as in this file.
It agrees with Definition 8.6.2 of [Neukirch–Schmidt–Wingberg].

The second context is when `A` is the `Kˢ`-valued points of a group scheme `J` such as an abelian
variety. Then the Tate–Shafarevich group is usually defined as the intersection of the kernels of
the maps `H¹(G_K, J(Kˢ)) → H¹(G_Kᵥ, J(Kᵥˢ))`. Note that in particular the module changes as well as
the group, so technically this is not quite what is happening in this definition. However the
inclusion `H¹(G_Kᵥ, J(Kᵥˢ)) → H¹(G_Kᵥ, J(Kˢ))` is an isomorphism by the Greenberg approximation
theorem, so the definition in this file is still mathematically correct.
See Remark I.3.10 of [Milne].

The third context is when `A` is the quotient of a `p`-adic `G_K`-module by a `G_K`-invariant
lattice, which is different from the definition in this PR. See Section 1 of [Flach].

## References

* [Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*](https://link.springer.com/book/10.1007/978-3-540-37889-1)
* [Milne, *Arithmetic Duality Theorems*](https://www.jmilne.org/math/Books/ADTnot.pdf)
* [Flach, *A finiteness theorem for the symmetric square of an elliptic curve*](https://link.springer.com/article/10.1007/BF01232029)
-/

section

universe u v

variable {K : Type u} {V : Type v} [Field K] (f : V → Type u) [∀ v, Field (f v)]
  [∀ v, Algebra K (f v)] (A : TopRep ℤ (Field.absoluteGaloisGroup K)) (n : ℕ)

open CategoryTheory

namespace ContinuousCohomology

/-- The Tate–Shafarevich group of a Galois module. -/
@[simps!]
noncomputable def tateShafarevich : AddSubgroup (continuousCohomology n A) :=
  ⨅ v, (map (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker

lemma tateShafarevich_eq_iInf : tateShafarevich f A n =
    ⨅ v : V, (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker := rfl

lemma tateShafarevich_eq_ker_pi : tateShafarevich f A n =
    (AddMonoidHom.pi fun v : V ↦ (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom).ker := by
  ext; simp [tateShafarevich_eq_iInf, funext_iff]

@[simp]
lemma mem_tateShafarevich (x : continuousCohomology n A) : x ∈ tateShafarevich f A n ↔
    ∀ v : V, (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom x = 0 := by
  simp [tateShafarevich_eq_iInf]

end ContinuousCohomology

end

/-
Copyright 2026 The Formal Conjectures Authors.

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
# The Tate–-Shafarevich group of an elliptic curve over a number field

The non-singular points over an algebraic closure of a field `K` carry a discrete Galois
representation. For a number field, the *Tate–Shafarevich group* is the intersection of the kernels
of restriction to all infinite and finite completions, where finite places are indexed by the
non-zero prime ideals of the ring of integers of `K`. The coefficient module remains the geometric
points over the separable closure of `K`, with its action restricted to each local Galois group.

## References

* [Silverman2009] Joseph H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts
  in Mathematics 106, Springer (2009), [doi](https://doi.org/10.1007/978-0-387-09494-6).
  Chapter X, §4, pp. 331–333, especially the definition on p. 332, gives the classical
  Tate–-Shafarevich group over a number field, using local geometric points.
* [J. S. Milne, Arithmetic Duality Theorems](https://www.jmilne.org/math/Books/ADTnot.pdf)
* [J. S. Milne, Elliptic Curves](https://www.jmilne.org/math/Books/EC2.pdf), 2nd ed., Chapter IV,
  Remark 1.11, p. 111, explains the use of a separable closure over imperfect fields.
-/

section

@[simp]
lemma Field.absoluteGaloisGroup.one_toAlgHom {K : Type*} [Field K] :
    (1 : Field.absoluteGaloisGroup K).toAlgHom = AlgHom.id K (AlgebraicClosure K) := rfl

@[simp]
lemma Field.absoluteGaloisGroup.mul_toAlgHom {K : Type*} [Field K]
    (σ τ : Field.absoluteGaloisGroup K) :
    (σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom := rfl

@[simp]
lemma WeierstrassCurve.Affine.Point.map_id' {R S F : Type*} [CommRing R] [CommRing S]
    [Field F] {W' : WeierstrassCurve.Affine R} [DecidableEq F] [Algebra R S] [Algebra R F]
    [Algebra S F] [IsScalarTower R S F] (P : (W'.baseChange F).Point) :
    WeierstrassCurve.Affine.Point.map (AlgHom.id S F) P = P := by
  cases P <;> rfl

lemma ContinuousLinearMap.mk_apply {R S M M₂ : Type*} [Semiring R] [Semiring S]
    {σ : R →+* S} [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R M] [Module S M₂] (toLinearMap : M →ₛₗ[σ] M₂)
    (cont : Continuous toLinearMap.toFun) (m : M) :
    ContinuousLinearMap.mk toLinearMap cont m = toLinearMap m := rfl

namespace WeierstrassCurve.Affine

open ContinuousCohomology IsDedekindDomain NumberField

variable {K : Type*} [Field K] (W : Affine K)

/-- The geometric non-singular points as a topological space. -/
local instance : TopologicalSpace (W⁄(AlgebraicClosure K)).Point := ⊥

/-- The geometric non-singular points equipped with the discrete topology. -/
local instance : DiscreteTopology (W⁄(AlgebraicClosure K)).Point := ⟨rfl⟩

open scoped Classical in
/-- The natural Galois action on geometric non-singular points with their discrete topology.

This uses `AlgebraicClosure K` to match `Field.absoluteGaloisGroup`. For number fields, which are
perfect, an algebraic closure is also a separable closure. Over an imperfect field, the coefficient
module for the usual Galois cohomology of an elliptic curve should use `SeparableClosure K` instead.

TODO: use `SeparableClosure K` for the coefficient field when the API for absolute Galois groups
supports this directly. The automorphism group of the algebraic closure itself gives the usual
absolute Galois group by restriction to the separable closure. -/
noncomputable def galoisRepresentation : TopRep ℤ <| Field.absoluteGaloisGroup K := .of <|
  .ofMonoidHom {
    toFun σ := { __ := (Affine.Point.map (W' := W) σ.toAlgHom).toIntLinearMap }
    map_one' := by ext; simp
    map_mul' σ τ := by ext; simp [ContinuousLinearMap.mk_apply _, Point.map_map] }

/-- The subgroup of the first continuous Galois cohomology group consisting of classes whose
restrictions vanish at every infinite and finite place. When `W.IsElliptic`, this is the classical
Tate--Shafarevich group of `W` over `K`. The construction also applies to the nonsingular locus
of a singular Weierstrass curve. -/
noncomputable def tateShafarevich [NumberField K] :
    AddSubgroup <| continuousCohomology 1 W.galoisRepresentation :=
  ContinuousCohomology.tateShafarevich
      (fun v : InfinitePlace K ↦ v.Completion) W.galoisRepresentation 1 ⊓
    ContinuousCohomology.tateShafarevich
      (fun v : HeightOneSpectrum <| 𝓞 K ↦ v.adicCompletion K) W.galoisRepresentation 1

end WeierstrassCurve.Affine

end

namespace Problem
universe u
abbrev Target : Prop := ∀ (K : Type u) [Field K] [NumberField K] (W : WeierstrassCurve.Affine K) [W.IsElliptic], Finite W.tateShafarevich
end Problem
