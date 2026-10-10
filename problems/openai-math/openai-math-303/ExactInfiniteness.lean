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

- problem_id: ExactInfiniteness
- collection: openai-math
- question_id: openai-math:303
- source: openai-math
- source_locator: lean/ComparatorChallenges/ExactInfiniteness.lean#OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the ordinary-to-strong pure-infiniteness question of Kirchberg and Rørdam for complex C∗-algebras. For exact algebras, proper infiniteness of one fixed finite amplification of every positive element also suffices. Consequently, every separable nuclear algebra with this property absorbs $`\mathcal O_\infty`$, without unitality or simplicity assumptions. ([Lean](lean/docs/303.md)) We prove that every complex C∗-algebra in which each positive element is properly infinite is strongly purely infinite. This answers the ordinary-to-strong part of Kirchberg–Rørdam's comparison question. For exact algebras, we also prove that proper infiniteness of one fixed finite amplification of every positive element implies proper infiniteness of each positive element. Consequently, every separable nuclear algebra with this fixed-amplification property absorbs $`\mathcal O_\infty`$, without assumptions of unitality or simplicity.
- notes: OpenAI math result family 303, Weak pure infiniteness and Cuntz-algebra absorption -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/303.md
- track: solved
- answer_shape: proof
- context_lemmas: norm_completion_le norm_completion
- source_theorem: OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite
- source_theorem_count: 2
- source_solution_module: OAI.Analysis.WeakInfiniteness.Main
- source_papers: preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf
- source_scope_note: lean/docs/303.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
universe u v
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
namespace WeakPureInfiniteness

section CompletedOperators

variable {domain codomain : Type*}
  [NormedAddCommGroup domain] [NormedSpace ℂ domain]
  [NormedAddCommGroup codomain] [NormedSpace ℂ codomain]

lemma norm_completion_le (operator : domain →L[ℂ] codomain) :
    ‖operator.completion‖ ≤ ‖operator‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg operator)
  intro vector
  induction vector using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih vector => simpa using operator.le_opNorm vector

lemma norm_completion (operator : domain →L[ℂ] codomain) :
    ‖operator.completion‖ = ‖operator‖ := by
  apply le_antisymm (norm_completion_le operator)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro vector
  simpa using operator.completion.le_opNorm (vector : Completion domain)

end CompletedOperators

structure ComplexHilbert where
  Carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [innerProductSpace : InnerProductSpace ℂ Carrier]
  [completeSpace : CompleteSpace Carrier]

attribute [instance] ComplexHilbert.normedAddCommGroup
  ComplexHilbert.innerProductSpace ComplexHilbert.completeSpace
instance : CoeSort ComplexHilbert.{u} (Type u) := ⟨ComplexHilbert.Carrier⟩

instance completedTensorCStar (H K : ComplexHilbert.{u}) :
    CStarAlgebra (Completion (H ⊗[ℂ] K) →L[ℂ] Completion (H ⊗[ℂ] K)) := inferInstance

instance hilbertOperatorsCStar (H : ComplexHilbert.{u}) :
    CStarAlgebra (H →L[ℂ] H) := inferInstance

structure SpatialRepresentation (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] where
  left : ComplexHilbert.{max u v}
  right : ComplexHilbert.{max u v}
  leftRep : A →⋆ₙₐ[ℂ] (left →L[ℂ] left)
  rightRep : B →⋆ₙₐ[ℂ] (right →L[ℂ] right)

abbrev SpatialRepresentation.hilbert {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (π : SpatialRepresentation A B) : ComplexHilbert.{max u v} where
  Carrier := Completion (π.left ⊗[ℂ] π.right)

abbrev SpatialRepresentation.space {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (π : SpatialRepresentation A B) := Completion (π.left ⊗[ℂ] π.right)

def SpatialAmbient (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] : Type (max u v + 1) :=
  lp (fun π : SpatialRepresentation A B => π.space →L[ℂ] π.space) ∞

instance spatialAmbientCStar (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (SpatialAmbient A B) := by
  unfold SpatialAmbient
  infer_instance

instance spatialAmbientCoeFun (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    CoeFun (SpatialAmbient A B) (fun _ => ∀ π : SpatialRepresentation A B, π.space →L[ℂ] π.space) :=
  ⟨fun z => z.val⟩

def spatialElementary {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (a : A) (b : B) : SpatialAmbient A B :=
  ⟨fun π => (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion,
    memℓp_infty ⟨‖a‖ * ‖b‖, by
      rintro _ ⟨π, rfl⟩
      dsimp only
      rw [norm_completion]
      exact (TensorProduct.norm_mapL_le _ _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π.leftRep a) (NonUnitalStarAlgHom.norm_apply_le π.rightRep b)
          (norm_nonneg _) (norm_nonneg _))⟩⟩

def minimalTensorSubalgebra (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalStarSubalgebra ℂ (SpatialAmbient A B) :=
  (NonUnitalStarAlgebra.adjoin ℂ (Set.range fun p : A × B => spatialElementary p.1 p.2)).topologicalClosure

abbrev MinimalTensor (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] := minimalTensorSubalgebra A B

instance (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (MinimalTensor A B) := by
  letI : IsClosed ((minimalTensorSubalgebra A B : NonUnitalStarSubalgebra ℂ
    (SpatialAmbient A B)) : Set (SpatialAmbient A B)) :=
    isClosed_closure
  exact inferInstance

section Exactness

variable {A : Type u} {C D : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def SpatialRepresentation.precompRight (π : SpatialRepresentation A D)
    (q : C →⋆ₙₐ[ℂ] D) : SpatialRepresentation A C where
  left := π.left
  right := π.right
  leftRep := π.leftRep
  rightRep := π.rightRep.comp q

def tensorKernelIdeal (q : C →⋆ₙₐ[ℂ] D) : NonUnitalStarSubalgebra ℂ (SpatialAmbient A C) :=
  (NonUnitalStarAlgebra.adjoin ℂ
    {z | ∃ a : A, ∃ c : C, q c = 0 ∧ z = spatialElementary a c}).topologicalClosure

end Exactness

def Exact (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ (C D : Type u) [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (q : C →⋆ₙₐ[ℂ] D), Function.Surjective q →
    ∀ z : MinimalTensor A C,
      (∀ π : SpatialRepresentation A D, (z.val : SpatialAmbient A C) (π.precompRight q) = 0) →
      z.val ∈ tensorKernelIdeal (A := A) q

section Definitions

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {m k : Type*} [Fintype m] [Fintype k]

def CuntzSubequiv (a : CStarMatrix m m A) (b : CStarMatrix k k A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ v : CStarMatrix k m A, ‖v.conjTranspose * b * v - a‖ < ε

def blockSum (a : CStarMatrix m m A) (b : CStarMatrix k k A) :
    CStarMatrix (m ⊕ k) (m ⊕ k) A :=
  CStarMatrix.ofMatrix (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm a) 0 0
    (CStarMatrix.ofMatrix.symm b))

def ProperlyInfinite (a : CStarMatrix m m A) : Prop :=
  CuntzSubequiv (blockSum a a) a

def diagonalCopies (n : ℕ) (a : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal fun _ => a)

variable (A)

def WeaklyPurelyInfinite : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a)

def StronglyPurelyInfinite : Prop :=
  ∀ a b : A, 0 ≤ a → 0 ≤ b → ∀ ε : ℝ, 0 < ε →
    ∃ s t : A, ‖star s * (a * a) * s - a * a‖ < ε ∧
      ‖star t * (b * b) * t - b * b‖ < ε ∧ ‖star s * a * b * t‖ < ε

end Definitions

def exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any_statement : Prop :=
  ∀ {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (hA : Exact A) (hW : WeaklyPurelyInfinite A) {a : A} (ha : 0 ≤ a),
    ProperlyInfinite (diagonalCopies 1 a)

def exact_weaklyPurelyInfinite_stronglyPurelyInfinite_statement : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (hExact : Exact A) (hWeak : WeaklyPurelyInfinite A),
    StronglyPurelyInfinite A

end WeakPureInfiniteness

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any_statement.{u} ∧
  _root_.OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite_statement.{u}

end Problem

/- Formalization scope, from lean/docs/303.md: The formalization proves that a complex $C^*$-algebra in which every positive element is properly infinite is strongly purely infinite, with the full positive-element diagonalization property. No exactness, nuclearity, unitality, or simplicity assumption is needed for this implication. For exact algebras, proper infiniteness of one fixed finite amplification of every positive element already implies individual proper infiniteness and strong pure infiniteness. -/
