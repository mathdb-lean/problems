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

- problem_id: SplitTangentIntegrability
- collection: openai-math
- question_id: openai-math:052
- source: openai-math
- source_locator: lean/ComparatorChallenges/SplitTangentIntegrability.lean#OAI.SplitTangent.integrability_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: A splitting of the tangent bundle of a compact Kähler manifold into two integrable holomorphic subbundles induces a compatible product decomposition of its universal cover, proving the two-summand form of Beauville's splitting conjecture. On smooth rationally connected projective manifolds, both summands are automatically integrable, establishing Höring's conjecture and the corresponding product decomposition. ([Lean](lean/docs/052.md)) We prove the two-summand form of Beauville's compatible splitting conjecture. If the tangent bundle of a compact connected Kähler manifold decomposes into two integrable holomorphic subbundles of positive rank, then its ordinary universal cover admits a product decomposition whose factor tangent bundles are the lifted specified summands. We prove that both summands of every specified holomorphic splitting of the tangent bundle of a smooth rationally connected projective complex manifold into two positive-rank subbundles are integrable. This proves Höring's conjecture on rationally connected projective manifolds. Höring's product theorem then gives a product decomposition compatible with the specified splitting.
- notes: OpenAI math result family 052, Tangent splittings and product decompositions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/052.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SplitTangent.integrability_main
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.SplitTangent.RationalVariation
- source_papers: preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf preprints/Integrability-of-split-tangent-bundles-on-rationally-connected-manifolds-September-23-2026/main.pdf
- source_scope_note: lean/docs/052.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

 

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u
namespace SplitTangent

 
structure ComplexManifold where
  dim : ℕ
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace (Fin dim → ℂ) Carrier]
  [holomorphicAtlas : IsManifold 𝓘(ℂ, Fin dim → ℂ) ω Carrier]
  [hausdorff : T2Space Carrier]
  [secondCountable : SecondCountableTopology Carrier]

attribute [instance] ComplexManifold.topology ComplexManifold.charts
  ComplexManifold.holomorphicAtlas ComplexManifold.hausdorff
  ComplexManifold.secondCountable

abbrev Model (X : ComplexManifold.{u}) := Fin X.dim → ℂ
abbrev ModelWithCorners (X : ComplexManifold.{u}) := 𝓘(ℂ, Model X)
abbrev Tangent (X : ComplexManifold.{u}) (x : X.Carrier) :=
  TangentSpace (ModelWithCorners X) x

abbrev ProjectiveSpace (N : ℕ) := ℙ ℂ (Fin (N + 1) → ℂ)

 

def projectiveCoordinates {N : ℕ} (i : Fin (N + 1))
    (p : ProjectiveSpace N) : Fin (N + 1) → ℂ :=
  fun j => (p.rep i)⁻¹ * p.rep j

 

structure ProjectiveEmbedding (X : ComplexManifold.{u}) where
  N : ℕ
  map : X.Carrier → ProjectiveSpace N
  injective : Function.Injective map
  open_patch : ∀ i, IsOpen {x | (map x).rep i ≠ 0}
  holomorphic : ∀ i, ContMDiffOn (ModelWithCorners X) 𝓘(ℂ, Fin (N + 1) → ℂ) ω
    (fun x => projectiveCoordinates i (map x)) {x | (map x).rep i ≠ 0}
  immersion : ∀ x i, (map x).rep i ≠ 0 → Function.Injective
    (mfderiv (ModelWithCorners X) 𝓘(ℂ, Fin (N + 1) → ℂ)
      (fun y => projectiveCoordinates i (map y)) x)

 
structure RationalCurve (X : ComplexManifold.{u}) where
  finite : ℂ → X.Carrier
  infinity : ℂ → X.Carrier
  finite_holomorphic : ContMDiff 𝓘(ℂ, ℂ) (ModelWithCorners X) ω finite
  infinity_holomorphic : ContMDiff 𝓘(ℂ, ℂ) (ModelWithCorners X) ω infinity
  overlap : ∀ z : ℂ, z ≠ 0 → finite z = infinity z⁻¹

def RationalCurve.value {X : ComplexManifold.{u}} (g : RationalCurve X)
    (z : OnePoint ℂ) : X.Carrier :=
  z.elim (g.infinity 0) g.finite

abbrev PairPolynomial (N : ℕ) := MvPolynomial (Fin 2 × Fin (N + 1)) ℂ

 
def Bihomogeneous {N : ℕ} (p : PairPolynomial N) : Prop :=
  ∃ a b : ℕ, ∀ m ∈ p.support,
    (∑ i : Fin (N + 1), m (0, i)) = a ∧
    (∑ i : Fin (N + 1), m (1, i)) = b

def pairEval {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
    (p : PairPolynomial e.N) (xy : X.Carrier × X.Carrier) : ℂ :=
  MvPolynomial.eval
    (fun k : Fin 2 × Fin (e.N + 1) =>
      if k.1 = 0 then (e.map xy.1).rep k.2 else (e.map xy.2).rep k.2) p

 

def IsZariskiOpenPair {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
    (U : Set (X.Carrier × X.Carrier)) : Prop :=
  ∃ equations : Set (PairPolynomial e.N),
    (∀ p ∈ equations, Bihomogeneous p) ∧
    U = {xy | ∃ p ∈ equations, pairEval e p xy ≠ 0}

 

def RationallyConnected {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) : Prop :=
  ∃ U : Set (X.Carrier × X.Carrier), IsZariskiOpenPair e U ∧ U.Nonempty ∧ Dense U ∧
    ∀ xy ∈ U, ∃ g : RationalCurve X, ∃ a b : OnePoint ℂ,
      g.value a = xy.1 ∧ g.value b = xy.2

 

structure TangentSplitting (X : ComplexManifold.{u}) where
  projector : ∀ x : X.Carrier, Tangent X x →L[ℂ] Tangent X x
  idempotent : ∀ x v, projector x (projector x v) = projector x v
  holomorphic : ContMDiff
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun v : TangentBundle (ModelWithCorners X) X.Carrier =>
      (⟨v.proj, projector v.proj v.2⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
  first_positive : ∀ x, 0 < Module.finrank ℂ (LinearMap.range (projector x).toLinearMap)
  second_positive : ∀ x, 0 < Module.finrank ℂ (LinearMap.ker (projector x).toLinearMap)

def TangentSplitting.first {X : ComplexManifold.{u}} (S : TangentSplitting X) (x : X.Carrier) :
    Submodule ℂ (Tangent X x) := LinearMap.range (S.projector x).toLinearMap

def TangentSplitting.second {X : ComplexManifold.{u}} (S : TangentSplitting X) (x : X.Carrier) :
    Submodule ℂ (Tangent X x) := LinearMap.ker (S.projector x).toLinearMap

 

def HolomorphicSectionOn (X : ComplexManifold.{u})
    (V : ∀ x : X.Carrier, Tangent X x) (U : Set X.Carrier) : Prop :=
  ContMDiffOn (ModelWithCorners X) ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun x => (⟨x, V x⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U

 
def Integrable (X : ComplexManifold.{u}) (D : ∀ x : X.Carrier, Submodule ℂ (Tangent X x)) : Prop :=
  ∀ U : Set X.Carrier, IsOpen U → ∀ V W : ∀ x : X.Carrier, Tangent X x,
    HolomorphicSectionOn X V U → HolomorphicSectionOn X W U →
    (∀ x ∈ U, V x ∈ D x) → (∀ x ∈ U, W x ∈ D x) →
    ∀ x ∈ U, VectorField.mlieBracketWithin (ModelWithCorners X) V W U x ∈ D x

 

def IntegrabilityStatement : Prop :=
  ∀ (X : ComplexManifold.{u}), ConnectedSpace X.Carrier → CompactSpace X.Carrier →
    2 ≤ X.dim → ∀ e : ProjectiveEmbedding X, RationallyConnected e →
    ∀ S : TangentSplitting X, Integrable X S.first ∧ Integrable X S.second

def integrability_main_statement : Prop :=
  IntegrabilityStatement.{u}

end SplitTangent

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.SplitTangent.integrability_main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/052.md: The splitting question asks whether a holomorphic decomposition of the tangent bundle comes from a product decomposition of the universal cover. The formalized result gives an affirmative answer for a compact connected Kähler manifold whose tangent bundle splits into two positive-rank, integrable holomorphic subbundles. The universal cover is a product of connected simply connected complex manifolds of the prescribed dimensions, and the differential identifies the two tangent factors with the original summands. Both integrability assumptions are required. Automatic integrability and the paper's additional corollaries are not included. The formalization proves integrability of both summands in a holomorphic splitting of the tangent bundle of a rationally connected projective manifold. More precisely, for a compact connected complex manifold of dimension at least two with a projective embedding witnessing rational connectedness, each positive-rank summand of a holomorphic tangent-bundle splitting is integrable. The paper's compatible product decomposition is a separate consequence, outside this selected statement. -/
