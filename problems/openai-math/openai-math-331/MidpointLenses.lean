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

- problem_id: MidpointLenses
- collection: openai-math
- question_id: openai-math:331
- source: openai-math
- source_locator: lean/ComparatorChallenges/MidpointLenses.lean#OAI.SegmentLenses.midpoint_lens_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a real reflexive Banach space with an asymptotically midpoint uniformly convex norm but no equivalent asymptotically uniformly convex norm, extending Baudier's separation to reflexive spaces. In the same space, depth-k countably branching diamonds require distortion at least $`\sqrt{1+k/12}`$, so midpoint uniform convexity does not force uniformly bounded diamond distortion even under reflexivity. ([Lean](lean/docs/331.md)) We construct a separable reflexive real Banach space whose given norm is asymptotically midpoint uniformly convex but which admits no asymptotically uniformly convex equivalent norm. Its averaged midpoint modulus is at least $`\sqrt{1+t^2/12}-1`$, and the countably branching diamond of depth k has distortion at least $`\sqrt{1+k/12}`$ in this space. This gives a negative answer to the reflexive diamond converse for asymptotic uniform convexifiability. For a real segment-forest dual with unbounded finite component heights and the real infinite-height coordinate predual, we bound the tail of an arbitrary displacement in a symmetric lens by $`2\sqrt{R^2-\|x\|^2}`$, where R is the lens radius and x is its finitely supported center. Both given norms are asymptotically midpoint uniformly convex, although neither space admits an equivalent asymptotically uniformly convex norm. The finite-height forest dual is reflexive. We derive quantitative distortion bounds for countably branching diamond graphs from midpoint estimates and direct tree energies. In the dual of a finite-height segment forest, every distortion-D embedding of the depth-k diamond satisfies $`D^2\ge1+k/4`$. The same bound holds in the infinite-height coordinate predual. We also obtain power-type distortion bounds for path-cost and recursive tree norms. For an infinite-dimensional real subspace of L1 whose unit ball is totally bounded in measure and whose norm has the Daugavet property, we compute the averaged midpoint and one-sided asymptotic moduli at every unit center. They are $`\max\{t/2,t-1\}`$ and $`\max\{0,t-2\}`$, respectively. The same weak-neighborhood geometry excludes every equivalent asymptotically uniformly convex norm. A quantitative realization of the Kadets–Werner construction supplies a space with both hypotheses. Four real Banach spaces defined by bounded tree potentials satisfy the averaged asymptotic midpoint bound $`\widehat\delta(t)\ge\sqrt{1+t^2/4}-1`$ for $`0\lt t\lt 1`$, while none admits an asymptotically uniformly convex (AUC) renorming. On finite-height trees, the globally constrained norm equals the least additive cost of a Hilbert vector and root paths. The quadratic path and segment-start outer Hilbert sums are reflexive and asymptotically midpoint uniformly convex, and admit no equivalent AUC norm. For a countably branching tree, the closed real L1 spans of products of independent exponential or Gaussian-square multipliers along its paths have positive averaged asymptotic midpoint moduli and admit no equivalent asymptotically uniformly convex norm. The renorming obstruction holds for every positive nonconstant mean-one multiplier with finite second moment. We study tree norms computed by two least nonnegative fields whose difference is the vector. For Euclidean child aggregation, two root-sum spaces have an averaged asymptotic midpoint modulus of at least $`t^3/128`$ for $`0\lt t\lt 1`$, including a reflexive joining-root space. A reflexive construction with a fixed zero root also satisfies a homogeneous cubic estimate. These spaces admit no equivalent asymptotically uniformly convex norm. We also obtain sixth-power and cubic estimates when the aggregation exponent depends on the height of a finite component.
- notes: OpenAI math result family 331, Reflexive midpoint convexity and diamond distortion -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/331.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SegmentLenses.midpoint_lens_main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.SegmentLenses.Main
- source_main_result: OAI.SegmentLenses.midpoint_lens_main
- source_papers: preprints/Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026/manuscript.pdf preprints/Midpoint-lenses-in-segment-spaces-September-27-2026/manuscript.pdf preprints/Diamond-distortion-from-midpoint-and-tree-energies-September-27-2026/manuscript.pdf preprints/Exact-asymptotic-moduli-in-a-Daugavet-subspace-of-L1-September-27-2026/manuscript.pdf preprints/Midpoint-convexity-from-bounded-tree-potentials-and-path-costs-September-27-2026/manuscript.pdf preprints/Independent-products-in-real-L1-asymptotic-midpoint-convexity-without-AUC-renormings-September-27-2026/manuscript.pdf preprints/Midpoint-convexity-from-two-recursive-potentials-September-27-2026/manuscript.pdf
- source_scope_note: lean/docs/331.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

/-!
# Segment tests, their completion, and coordinate functionals
-/



open scoped BigOperators
open Finset

namespace SegmentLenses

abbrev InfiniteVertex := List ℕ

def ForestVertex := {p : ℕ × List ℕ // 1 ≤ p.1 ∧ p.2.length ≤ p.1}

def ForestAncestor (a b : ForestVertex) : Prop :=
  a.val.1 = b.val.1 ∧ a.val.2.IsPrefix b.val.2

def IsInterval {V : Type*} (ancestor : V → V → Prop) (S : Finset V) : Prop :=
  ∃ a b, ancestor a b ∧ ∀ v, v ∈ S ↔ ancestor a v ∧ ancestor v b

def Ancestral {V : Type*} (ancestor : V → V → Prop) (H : Finset V) : Prop :=
  ∀ ⦃a b⦄, b ∈ H → ancestor a b → a ∈ H

class SegmentSystem (V : Type*) where
  isSegment : Finset V → Prop
  singleton : ∀ v, isSegment {v}

structure SegmentFamily (V : Type*) [SegmentSystem V] where
  sets : Finset (Finset V)
  segment : ∀ S ∈ sets, SegmentSystem.isSegment S
  disjoint : (sets : Set (Finset V)).PairwiseDisjoint id

namespace SegmentFamily

variable {V : Type*} [SegmentSystem V]

def column (F : SegmentFamily V) (v : V) : EuclideanSpace ℝ F.sets :=
  by classical exact WithLp.toLp 2 (fun S => if v ∈ S.val then 1 else 0)

def test (F : SegmentFamily V) : (V →₀ ℝ) →ₗ[ℝ] EuclideanSpace ℝ F.sets :=
  Finsupp.linearCombination ℝ F.column

def seminorm (F : SegmentFamily V) : Seminorm ℝ (V →₀ ℝ) :=
  (normSeminorm ℝ (EuclideanSpace ℝ F.sets)).comp F.test

def singleton (v : V) : SegmentFamily V where
  sets := {{v}}
  segment := by
    intro S h
    have he : S = {v} := Finset.mem_singleton.mp h
    rw [he]
    exact SegmentSystem.singleton v
  disjoint := by
    intro S hS T hT hne
    simp only [Finset.mem_coe, Finset.mem_singleton] at hS hT
    exact False.elim (hne (hS.trans hT.symm))

end SegmentFamily

def segmentSeminorm (V : Type*) [SegmentSystem V] : Seminorm ℝ (V →₀ ℝ) :=
  ⨆ F : SegmentFamily V, F.seminorm

def Test (V : Type*) := V →₀ ℝ

namespace Test

variable {V : Type*}
instance : AddCommGroup (Test V) := inferInstanceAs (AddCommGroup (V →₀ ℝ))
instance : Module ℝ (Test V) := inferInstanceAs (Module ℝ (V →₀ ℝ))

def coeff (u : Test V) : V →₀ ℝ := u

def ofFinsupp (u : V →₀ ℝ) : Test V := u

variable [SegmentSystem V]
instance : Norm (Test V) where norm u := segmentSeminorm V u.coeff

instance : NormedAddCommGroup (Test V) := by
  have norm_column_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (v : V) : ‖F.column v‖ ≤ 1 := by
    classical
    by_cases hv : ∃ S ∈ F.sets, v ∈ S
    · obtain ⟨S, hS, hvS⟩ := hv
      have he : F.column v = PiLp.single 2 (⟨S, hS⟩ : F.sets) (1 : ℝ) := by
        ext T
        change (if v ∈ T.val then (1 : ℝ) else 0) = _
        by_cases hTS : T = ⟨S, hS⟩
        · subst T
          simp [hvS]
        · have hn : v ∉ T.val := by
            intro hvT
            have hne : T.val ≠ S := fun h => hTS (Subtype.ext h)
            exact Finset.disjoint_left.mp (F.disjoint T.property hS hne) hvT hvS
          simp [hTS, hn]
      rw [he, PiLp.norm_single]
      norm_num
    · have he : F.column v = 0 := by
        ext S
        have hn : v ∉ S.val := fun h => hv ⟨S.val, S.property, h⟩
        simp [SegmentFamily.column, hn]
      rw [he, norm_zero]
      norm_num
  have test_apply {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) (S : F.sets) :
      F.test u S = ∑ v ∈ S.val, u v := by
    classical
    simp only [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum,
      WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, SegmentFamily.column,
      smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_subset
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv hnv
      have hnot : v ∉ u.support := by
        intro hvs
        exact hnv (Finset.mem_filter.mpr ⟨hvs, hv⟩)
      exact Finsupp.notMem_support_iff.mp hnot
  have norm_test_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      ‖F.test u‖ ≤ ∑ v ∈ u.support, |u v| := by
    classical
    rw [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum]
    calc
      ‖∑ v ∈ u.support, u v • F.column v‖ ≤
          ∑ v ∈ u.support, ‖u v • F.column v‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (norm_column_le F v)
  have seminorm_sq {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      F.seminorm u ^ 2 = ∑ S : F.sets, (∑ v ∈ S.val, u v) ^ 2 := by
    change ‖F.test u‖ ^ 2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro S _
    rw [test_apply]
  have singleton_seminorm {V : Type _} [SegmentSystem V] (v : V) (u : V →₀ ℝ) :
      (SegmentFamily.singleton v).seminorm u = |u v| := by
    have h := seminorm_sq (SegmentFamily.singleton v) u
    have hh : (∑ S : (SegmentFamily.singleton v).sets, (∑ w ∈ S.val, u w) ^ 2) = u v ^ 2 := by
      exact (Finset.sum_coe_sort (SegmentFamily.singleton v).sets
        (fun S : Finset V => (∑ w ∈ S, u w) ^ 2)).trans (by simp [SegmentFamily.singleton])
    rw [hh] at h
    have hn := apply_nonneg (SegmentFamily.singleton v).seminorm u
    nlinarith [sq_abs (u v), abs_nonneg (u v)]
  have segmentTests_bdd (V : Type _) [SegmentSystem V] :
      BddAbove (Set.range (SegmentFamily.seminorm (V := V))) := by
    rw [Seminorm.bddAbove_iff]
    refine ⟨fun u => ∑ v ∈ u.support, |u v|, ?_⟩
    rintro _ ⟨p, ⟨F, rfl⟩, rfl⟩ u
    exact norm_test_le F u
  have le_segmentSeminorm {V : Type _} [SegmentSystem V]
      (F : SegmentFamily V) (u : V →₀ ℝ) : F.seminorm u ≤ segmentSeminorm V u := by
    have h := le_ciSup (f := fun G : SegmentFamily V => G.seminorm) (segmentTests_bdd V) F
    exact Seminorm.le_def.mp h u
  have abs_coord_le {V : Type _} [SegmentSystem V] (u : V →₀ ℝ) (v : V) :
      |u v| ≤ segmentSeminorm V u := by
    rw [← singleton_seminorm v u]
    exact le_segmentSeminorm _ _
  have segmentSeminorm_eq_zero {V : Type _} [SegmentSystem V] (u : V →₀ ℝ) :
      segmentSeminorm V u = 0 ↔ u = 0 := by
    constructor
    · intro h
      ext v
      have hh := abs_coord_le u v
      rw [h] at hh
      simpa using hh
    · rintro rfl
      exact map_zero _
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    norm_nonneg u := apply_nonneg (segmentSeminorm V) u.coeff
    norm_smul c u := map_smul_eq_mul (segmentSeminorm V) c u.coeff
    norm_triangle u v := map_add_le_add (segmentSeminorm V) u.coeff v.coeff
    norm_eq_zero_iff u := segmentSeminorm_eq_zero u.coeff }
instance : NormedSpace ℝ (Test V) where
  norm_smul_le c u := le_of_eq (map_smul_eq_mul (segmentSeminorm V) c u.coeff)

def evaluation (v : V) : Test V →L[ℝ] ℝ := by
  have norm_column_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (v : V) : ‖F.column v‖ ≤ 1 := by
    classical
    by_cases hv : ∃ S ∈ F.sets, v ∈ S
    · obtain ⟨S, hS, hvS⟩ := hv
      have he : F.column v = PiLp.single 2 (⟨S, hS⟩ : F.sets) (1 : ℝ) := by
        ext T
        change (if v ∈ T.val then (1 : ℝ) else 0) = _
        by_cases hTS : T = ⟨S, hS⟩
        · subst T
          simp [hvS]
        · have hn : v ∉ T.val := by
            intro hvT
            have hne : T.val ≠ S := fun h => hTS (Subtype.ext h)
            exact Finset.disjoint_left.mp (F.disjoint T.property hS hne) hvT hvS
          simp [hTS, hn]
      rw [he, PiLp.norm_single]
      norm_num
    · have he : F.column v = 0 := by
        ext S
        have hn : v ∉ S.val := fun h => hv ⟨S.val, S.property, h⟩
        simp [SegmentFamily.column, hn]
      rw [he, norm_zero]
      norm_num
  have test_apply {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) (S : F.sets) :
      F.test u S = ∑ v ∈ S.val, u v := by
    classical
    simp only [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum,
      WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, SegmentFamily.column,
      smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_subset
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv hnv
      have hnot : v ∉ u.support := by
        intro hvs
        exact hnv (Finset.mem_filter.mpr ⟨hvs, hv⟩)
      exact Finsupp.notMem_support_iff.mp hnot
  have norm_test_le {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      ‖F.test u‖ ≤ ∑ v ∈ u.support, |u v| := by
    classical
    rw [SegmentFamily.test, Finsupp.linearCombination_apply, Finsupp.sum]
    calc
      ‖∑ v ∈ u.support, u v • F.column v‖ ≤
          ∑ v ∈ u.support, ‖u v • F.column v‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (norm_column_le F v)
  have seminorm_sq {V : Type _} [SegmentSystem V] (F : SegmentFamily V) (u : V →₀ ℝ) :
      F.seminorm u ^ 2 = ∑ S : F.sets, (∑ v ∈ S.val, u v) ^ 2 := by
    change ‖F.test u‖ ^ 2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro S _
    rw [test_apply]
  have singleton_seminorm {V : Type _} [SegmentSystem V] (v : V) (u : V →₀ ℝ) :
      (SegmentFamily.singleton v).seminorm u = |u v| := by
    have h := seminorm_sq (SegmentFamily.singleton v) u
    have hh : (∑ S : (SegmentFamily.singleton v).sets, (∑ w ∈ S.val, u w) ^ 2) = u v ^ 2 := by
      exact (Finset.sum_coe_sort (SegmentFamily.singleton v).sets
        (fun S : Finset V => (∑ w ∈ S, u w) ^ 2)).trans (by simp [SegmentFamily.singleton])
    rw [hh] at h
    have hn := apply_nonneg (SegmentFamily.singleton v).seminorm u
    nlinarith [sq_abs (u v), abs_nonneg (u v)]
  have segmentTests_bdd (V : Type _) [SegmentSystem V] :
      BddAbove (Set.range (SegmentFamily.seminorm (V := V))) := by
    rw [Seminorm.bddAbove_iff]
    refine ⟨fun u => ∑ v ∈ u.support, |u v|, ?_⟩
    rintro _ ⟨p, ⟨F, rfl⟩, rfl⟩ u
    exact norm_test_le F u
  have le_segmentSeminorm {V : Type _} [SegmentSystem V]
      (F : SegmentFamily V) (u : V →₀ ℝ) : F.seminorm u ≤ segmentSeminorm V u := by
    have h := le_ciSup (f := fun G : SegmentFamily V => G.seminorm) (segmentTests_bdd V) F
    exact Seminorm.le_def.mp h u
  have abs_coord_le {V : Type _} [SegmentSystem V] (u : V →₀ ℝ) (v : V) :
      |u v| ≤ segmentSeminorm V u := by
    rw [← singleton_seminorm v u]
    exact le_segmentSeminorm _ _
  exact let f : Test V →ₗ[ℝ] ℝ :=
      { toFun := fun u => u.coeff v
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    f.mkContinuous 1 (fun u => by
      change |u.coeff v| ≤ 1 * segmentSeminorm V u.coeff
      simpa only [one_mul] using abs_coord_le u.coeff v)

end Test

abbrev Primal (V : Type*) [SegmentSystem V] := UniformSpace.Completion (Test V)

abbrev FullDual (V : Type*) [SegmentSystem V] := StrongDual ℝ (Primal V)

def unitVector {V : Type*} [SegmentSystem V] (v : V) : Primal V :=
  (Test.ofFinsupp (Finsupp.single v 1) : Test V)

def coordinate {V : Type*} [SegmentSystem V] (v : V) : FullDual V :=
  (Test.evaluation v).extend UniformSpace.Completion.toComplL

def coordinateSpan (V : Type*) [SegmentSystem V] : Submodule ℝ (FullDual V) :=
  (Submodule.span ℝ (Set.range (coordinate (V := V)))).topologicalClosure

abbrev CoordinatePredual (V : Type*) [SegmentSystem V] : Type _ := ↥(coordinateSpan V)

def head {V : Type*} [SegmentSystem V] (H : Finset V) (x : FullDual V) : FullDual V :=
  ∑ v ∈ H, x (unitVector v) • coordinate v

def tail {V : Type*} [SegmentSystem V] (H : Finset V) (x : FullDual V) : FullDual V :=
  x - head H x

instance infiniteSegments : SegmentSystem InfiniteVertex where
  isSegment := IsInterval List.IsPrefix
  singleton v := by
    refine ⟨v, v, List.prefix_rfl, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl; exact ⟨List.prefix_rfl, List.prefix_rfl⟩
    · rintro ⟨hvw, hwv⟩
      exact hwv.eq_of_length (Nat.le_antisymm hwv.length_le hvw.length_le)

instance forestSegments : SegmentSystem ForestVertex where
  isSegment := IsInterval ForestAncestor
  singleton v := by
    refine ⟨v, v, ⟨rfl, List.prefix_rfl⟩, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl; exact ⟨⟨rfl, List.prefix_rfl⟩, ⟨rfl, List.prefix_rfl⟩⟩
    · rintro ⟨hvw, hwv⟩
      exact Subtype.ext (Prod.ext hwv.1 (hwv.2.eq_of_length (Nat.le_antisymm hwv.2.length_le hvw.2.length_le)))

abbrev J := Primal ForestVertex

abbrev X := FullDual ForestVertex

abbrev JInfinite := Primal InfiniteVertex

abbrev BInfinite := CoordinatePredual InfiniteVertex

def midpoint_lens_main_statement : Prop :=
  (∀ (H : Finset ForestVertex) (_ : Ancestral ForestAncestor H)
      (x y : X) (_ : x = head H x) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) ∧
    (∀ (H : Finset InfiniteVertex) (_ : Ancestral List.IsPrefix H)
      (x y : BInfinite) (_ : x.val = head H x.val) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y.val‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2))

end SegmentLenses

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SegmentLenses.midpoint_lens_main_statement

end Problem

/- Formalization scope, from lean/docs/331.md: The paper constructs a Banach space whose midpoint geometry is asymptotically uniformly convex even though no equivalent norm is asymptotically uniformly convex in the usual one-sided sense. The formalization proves that the full dual of the specified segment-norm completion is infinite-dimensional, separable, and reflexive; its averaged midpoint modulus is at least $\sqrt{1+t^2/12}-1$ for every $t>0$, while every equivalent norm fails asymptotic uniform convexity. It also proves that an embedding of a depth-$k$ countably branching diamond has distortion at least $\sqrt{1+k/12}$. The general-forest and word-forest results use the closed span of the coordinate functionals. Their conclusions retain the finite-ancestor and equivalent-norm hypotheses, including the scale $\alpha/(2\beta)$ when $0<\alpha\le\beta$ and the new norm lies between $\alpha$ and $\beta$ times the original norm; they do not identify that span with the full dual or assert reflexivity for every forest. The paper controls midpoint lenses in Banach spaces defined by tree-segment norms. The formalization proves the following estimate in both the full dual of the finite-height forest space and the coordinate predual of the infinite-tree space. If $x$ is supported on a finite ancestral set $H$, $R\ge0$, and $\|x+y\|,\|x-y\|\le R$, then the part of $y$ outside $H$ has norm at most $2\sqrt{R^2-\|x\|^2}$. The formalization also covers selected consequences for averaged midpoint moduli and separated families of vectors, together with reflexivity and renorming obstructions. This scope concerns the segment-space results; the companion results on diamond energies remain separate. The paper studies embeddings of countably branching diamond graphs into Banach spaces built from tree segments. The formalization proves that every embedding of the depth-$k$ diamond with distortion $D$, at any positive scale, satisfies $1+k/4\le D^2$ in either of two spaces: the full dual of the completed finite-height forest space and the closed coordinate span in the dual of the infinite-tree space. The bound applies to all pairs of vertices and is unconditional. The formalization also contains selected graph deductions under explicit companion assumptions. Twenty-two of those companion inputs are assumed in these deductions; the diamond distortion bound above does not require them. The paper exhibits a real $L_1$ subspace with positive averaged midpoint convexity but no equivalent asymptotically uniformly convex norm. For every closed infinite-dimensional subspace whose unit ball is precompact in measure and which has the Daugavet property, the formalization computes the moduli at every unit vector: the averaged midpoint modulus is $\max(t/2,t-1)$ and the usual one-sided asymptotic modulus is $\max(0,t-2)$ for every $t>0$. The same formulas hold after taking the infimum over unit vectors, and every equivalent norm fails asymptotic uniform convexity. The formalization also constructs such a subspace on a countable product of unit intervals and proves that it has the stated measure-precompactness and Daugavet properties, so the modulus formulas apply to an actual example. The paper constructs Banach spaces from bounded tree potentials and path costs to separate averaged midpoint convexity from asymptotic uniform convexity. For the specified tree-potential completions, the formalization proves completeness, separability, infinite dimension, and an averaged midpoint modulus of at least $\sqrt{1+t^2/4}-1$ for $0<t<1$. No space linearly isomorphic to one of these completions is asymptotically uniformly convex. The formalization also covers selected path-cost duality and comparison results, clipping and energy estimates, and further renorming obstructions. These retain their stated support, head, and tail hypotheses; the remaining auxiliary assertions of the paper are outside this scope. The paper forms a real $L_1$ space from the closed span of products of independent multipliers along tree paths. For a positive, nonconstant multiplier of mean one and finite second moment, the formalization proves that this space is infinite-dimensional and has no equivalent asymptotically uniformly convex norm. For every $t>0$, the averaged midpoint modulus nevertheless has explicit positive lower bounds. If $G$ is a standard real Gaussian, the exponential-multiplier bound is $\frac{7t}{480}\mathbb E[(|G|-20/t)_+]$, where $u_+=\max(u,0)$. For squared-Gaussian multipliers, the bounds are $\frac18\Pr(|G|\ge4\sqrt2(2+\sqrt2)/t)$ and $\frac14\Pr(|G|\ge8\sqrt6/t)$. The paper constructs three Banach spaces from recursive tree potentials: a root-sum space, a zero-root space, and a joined space. The formalization proves that all three are infinite-dimensional and have no equivalent asymptotically uniformly convex norm. The root-sum and joined spaces have averaged midpoint modulus at least $t^3/128$ for $0<t<1$, and the root-sum modulus is positive for every $t>0$. The zero-root estimate retains its finite ancestral support and tail hypotheses, and the zero-root and joined spaces are reflexive. The formalization also covers a separated-midpoint result for the joined space and a variable-exponent model with its recursive norm, duality, projections, renorming obstruction, and sixth- and third-order stability estimates. The separation, sequence, support, and head assumptions in these results are essential parts of their statements. -/
