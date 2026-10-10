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

- problem_id: DiamondDistortion
- collection: openai-math
- question_id: openai-math:331
- source: openai-math
- source_locator: lean/ComparatorChallenges/DiamondDistortion.lean#OAI.DiamondDistortion.headline_all_pairs
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a real reflexive Banach space with an asymptotically midpoint uniformly convex norm but no equivalent asymptotically uniformly convex norm, extending Baudier's separation to reflexive spaces. In the same space, depth-k countably branching diamonds require distortion at least $`\sqrt{1+k/12}`$, so midpoint uniform convexity does not force uniformly bounded diamond distortion even under reflexivity. ([Lean](lean/docs/331.md)) We construct a separable reflexive real Banach space whose given norm is asymptotically midpoint uniformly convex but which admits no asymptotically uniformly convex equivalent norm. Its averaged midpoint modulus is at least $`\sqrt{1+t^2/12}-1`$, and the countably branching diamond of depth k has distortion at least $`\sqrt{1+k/12}`$ in this space. This gives a negative answer to the reflexive diamond converse for asymptotic uniform convexifiability. For a real segment-forest dual with unbounded finite component heights and the real infinite-height coordinate predual, we bound the tail of an arbitrary displacement in a symmetric lens by $`2\sqrt{R^2-\|x\|^2}`$, where R is the lens radius and x is its finitely supported center. Both given norms are asymptotically midpoint uniformly convex, although neither space admits an equivalent asymptotically uniformly convex norm. The finite-height forest dual is reflexive. We derive quantitative distortion bounds for countably branching diamond graphs from midpoint estimates and direct tree energies. In the dual of a finite-height segment forest, every distortion-D embedding of the depth-k diamond satisfies $`D^2\ge1+k/4`$. The same bound holds in the infinite-height coordinate predual. We also obtain power-type distortion bounds for path-cost and recursive tree norms. For an infinite-dimensional real subspace of L1 whose unit ball is totally bounded in measure and whose norm has the Daugavet property, we compute the averaged midpoint and one-sided asymptotic moduli at every unit center. They are $`\max\{t/2,t-1\}`$ and $`\max\{0,t-2\}`$, respectively. The same weak-neighborhood geometry excludes every equivalent asymptotically uniformly convex norm. A quantitative realization of the Kadets–Werner construction supplies a space with both hypotheses. Four real Banach spaces defined by bounded tree potentials satisfy the averaged asymptotic midpoint bound $`\widehat\delta(t)\ge\sqrt{1+t^2/4}-1`$ for $`0\lt t\lt 1`$, while none admits an asymptotically uniformly convex (AUC) renorming. On finite-height trees, the globally constrained norm equals the least additive cost of a Hilbert vector and root paths. The quadratic path and segment-start outer Hilbert sums are reflexive and asymptotically midpoint uniformly convex, and admit no equivalent AUC norm. For a countably branching tree, the closed real L1 spans of products of independent exponential or Gaussian-square multipliers along its paths have positive averaged asymptotic midpoint moduli and admit no equivalent asymptotically uniformly convex norm. The renorming obstruction holds for every positive nonconstant mean-one multiplier with finite second moment. We study tree norms computed by two least nonnegative fields whose difference is the vector. For Euclidean child aggregation, two root-sum spaces have an averaged asymptotic midpoint modulus of at least $`t^3/128`$ for $`0\lt t\lt 1`$, including a reflexive joining-root space. A reflexive construction with a fixed zero root also satisfies a homogeneous cubic estimate. These spaces admit no equivalent asymptotically uniformly convex norm. We also obtain sixth-power and cubic estimates when the aggregation exponent depends on the height of a finite component.
- notes: OpenAI math result family 331, Reflexive midpoint convexity and diamond distortion -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/331.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.DiamondDistortion.headline_all_pairs
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.DiamondDistortion.Descent
- source_main_result: OAI.DiamondDistortion.headline_all_pairs
- source_papers: preprints/Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026/manuscript.pdf preprints/Midpoint-lenses-in-segment-spaces-September-27-2026/manuscript.pdf preprints/Diamond-distortion-from-midpoint-and-tree-energies-September-27-2026/manuscript.pdf preprints/Exact-asymptotic-moduli-in-a-Daugavet-subspace-of-L1-September-27-2026/manuscript.pdf preprints/Midpoint-convexity-from-bounded-tree-potentials-and-path-costs-September-27-2026/manuscript.pdf preprints/Independent-products-in-real-L1-asymptotic-midpoint-convexity-without-AUC-renormings-September-27-2026/manuscript.pdf preprints/Midpoint-convexity-from-two-recursive-potentials-September-27-2026/manuscript.pdf
- source_scope_note: lean/docs/331.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

universe u v


open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

structure SegmentSystem (ι : Type*) where
  IsSegment : Finset ι → Prop
  singleton : ∀ v, IsSegment {v}

namespace SegmentSystem

variable {ι : Type*} (T : SegmentSystem ι)

/-- The represented disjoint families in the definition of the primal segment norm. -/
structure Family where
  n : ℕ
  seg : Fin n → Finset ι
  allowed : ∀ i, T.IsSegment (seg i)
  disjoint : Pairwise (fun i j => Disjoint (seg i) (seg j))

instance : Nonempty T.Family := ⟨{
  n := 0
  seg := Fin.elim0
  allowed := fun i => Fin.elim0 i
  disjoint := fun {i} => Fin.elim0 i }⟩

variable {T}

/-- Segment testing as a Euclidean-valued linear map. -/
def Family.test (F : T.Family) : (ι →₀ ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin F.n) where
  toFun u := WithLp.toLp 2 (fun i => ∑ v ∈ F.seg i, u v)
  map_add' u v := by
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' c u := by
    ext i
    simp [Finset.mul_sum]

def Family.seminorm (F : T.Family) : Seminorm ℝ (ι →₀ ℝ) :=
  (normSeminorm ℝ (EuclideanSpace ℝ (Fin F.n))).comp F.test

variable (T)

def primalSeminorm : Seminorm ℝ (ι →₀ ℝ) := ⨆ F : T.Family, F.seminorm

/-- Singleton families ensure that the segment seminorm separates points. -/
def singletonFamily (v : ι) : T.Family where
  n := 1
  seg _ := {v}
  allowed _ := T.singleton v
  disjoint := by intro i j h; exact False.elim (h (Subsingleton.elim _ _))

def Primal (_T : SegmentSystem ι) := ι →₀ ℝ

instance : AddCommGroup T.Primal := inferInstanceAs (AddCommGroup (ι →₀ ℝ))
instance : Module ℝ T.Primal := inferInstanceAs (Module ℝ (ι →₀ ℝ))

instance : NormedAddCommGroup T.Primal := by
  have Family.test_apply (F : T.Family) (u : ι →₀ ℝ) (i : Fin F.n) :
      F.test u i = ∑ v ∈ F.seg i, u v := rfl
  have Family.seminorm_apply (F : T.Family) (u : ι →₀ ℝ) :
      F.seminorm u = ‖F.test u‖ := rfl
  have Family.test_single_le (F : T.Family) (v : ι) (r : ℝ) :
      ‖F.test (Finsupp.single v r)‖ ≤ |r| := by
    classical
    rw [EuclideanSpace.norm_eq]
    apply (Real.sqrt_le_left (abs_nonneg r)).2
    by_cases h : ∃ i, v ∈ F.seg i
    · obtain ⟨i, hi⟩ := h
      have hne : ∀ j, j ≠ i → v ∉ F.seg j := by
        intro j hji hj
        exact Finset.disjoint_left.mp (F.disjoint hji) hj hi
      rw [Finset.sum_eq_single i]
      · simp [Family.test, Finsupp.single_apply, hi]
      · intro j _ hji
        simp [Family.test, Finsupp.single_apply, hne j hji]
      · simp
    · have hn : ∀ i, v ∉ F.seg i := by simpa using h
      simp [Family.test, Finsupp.single_apply, hn, sq_nonneg]
  have Family.test_le_l1 (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ u.sum (fun _ r => |r|) := by
    classical
    calc
      ‖F.test u‖ = ‖∑ v ∈ u.support, F.test (Finsupp.single v (u v))‖ := by
        rw [← map_sum]
        congr 2
        exact (Finsupp.sum_single u).symm
      _ ≤ ∑ v ∈ u.support, ‖F.test (Finsupp.single v (u v))‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := Finset.sum_le_sum fun v _ => Family.test_single_le F v (u v)
      _ = u.sum (fun _ r => |r|) := rfl
  have families_bddAbove : BddAbove (Set.range (Family.seminorm (T := T))) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    exact ⟨u.sum (fun _ r => |r|), by rintro _ ⟨F, rfl⟩; exact Family.test_le_l1 F u⟩
  have test_le_primal (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ T.primalSeminorm u := by
    rw [primalSeminorm, Seminorm.iSup_apply families_bddAbove]
    exact le_ciSup (⟨u.sum (fun _ r => |r|), by
      rintro _ ⟨G, rfl⟩; exact Family.test_le_l1 G u⟩ :
      BddAbove (Set.range (fun G : T.Family => G.seminorm u))) F
  have coordinate_le_primal (u : ι →₀ ℝ) (v : ι) : |u v| ≤ T.primalSeminorm u := by
    have h := test_le_primal (T.singletonFamily v) u
    rw [EuclideanSpace.norm_eq] at h
    change Real.sqrt (∑ _ : Fin 1, ‖∑ w ∈ ({v} : Finset ι), u w‖ ^ 2) ≤ _ at h
    simpa [Real.sqrt_sq_eq_abs] using h
  have primal_eq_zero_iff (u : ι →₀ ℝ) : T.primalSeminorm u = 0 ↔ u = 0 := by
    constructor
    · intro h
      ext v
      have := coordinate_le_primal u v
      simpa [h] using this
    · rintro rfl
      exact map_zero _
  exact AddGroupNorm.toNormedAddCommGroup
    { T.primalSeminorm.toAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun u h => (primal_eq_zero_iff u).mp h }

instance : NormedSpace ℝ T.Primal where
  norm_smul_le c u := le_of_eq (T.primalSeminorm.smul' c u)

abbrev JamesSpace := UniformSpace.Completion T.Primal

/-- Its full real continuous dual. -/
abbrev Dual := StrongDual ℝ T.JamesSpace

/-- Coordinate evaluation on finite arrays, bounded by the singleton test. -/
def coordinateFinite (v : ι) : T.Primal →L[ℝ] ℝ := by
  have Family.test_apply (F : T.Family) (u : ι →₀ ℝ) (i : Fin F.n) :
      F.test u i = ∑ v ∈ F.seg i, u v := rfl
  have Family.seminorm_apply (F : T.Family) (u : ι →₀ ℝ) :
      F.seminorm u = ‖F.test u‖ := rfl
  have Family.test_single_le (F : T.Family) (v : ι) (r : ℝ) :
      ‖F.test (Finsupp.single v r)‖ ≤ |r| := by
    classical
    rw [EuclideanSpace.norm_eq]
    apply (Real.sqrt_le_left (abs_nonneg r)).2
    by_cases h : ∃ i, v ∈ F.seg i
    · obtain ⟨i, hi⟩ := h
      have hne : ∀ j, j ≠ i → v ∉ F.seg j := by
        intro j hji hj
        exact Finset.disjoint_left.mp (F.disjoint hji) hj hi
      rw [Finset.sum_eq_single i]
      · simp [Family.test, Finsupp.single_apply, hi]
      · intro j _ hji
        simp [Family.test, Finsupp.single_apply, hne j hji]
      · simp
    · have hn : ∀ i, v ∉ F.seg i := by simpa using h
      simp [Family.test, Finsupp.single_apply, hn, sq_nonneg]
  have Family.test_le_l1 (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ u.sum (fun _ r => |r|) := by
    classical
    calc
      ‖F.test u‖ = ‖∑ v ∈ u.support, F.test (Finsupp.single v (u v))‖ := by
        rw [← map_sum]
        congr 2
        exact (Finsupp.sum_single u).symm
      _ ≤ ∑ v ∈ u.support, ‖F.test (Finsupp.single v (u v))‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ u.support, |u v| := Finset.sum_le_sum fun v _ => Family.test_single_le F v (u v)
      _ = u.sum (fun _ r => |r|) := rfl
  have families_bddAbove : BddAbove (Set.range (Family.seminorm (T := T))) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    exact ⟨u.sum (fun _ r => |r|), by rintro _ ⟨F, rfl⟩; exact Family.test_le_l1 F u⟩
  have test_le_primal (F : T.Family) (u : ι →₀ ℝ) :
      ‖F.test u‖ ≤ T.primalSeminorm u := by
    rw [primalSeminorm, Seminorm.iSup_apply families_bddAbove]
    exact le_ciSup (⟨u.sum (fun _ r => |r|), by
      rintro _ ⟨G, rfl⟩; exact Family.test_le_l1 G u⟩ :
      BddAbove (Set.range (fun G : T.Family => G.seminorm u))) F
  have coordinate_le_primal (u : ι →₀ ℝ) (v : ι) : |u v| ≤ T.primalSeminorm u := by
    have h := test_le_primal (T.singletonFamily v) u
    rw [EuclideanSpace.norm_eq] at h
    change Real.sqrt (∑ _ : Fin 1, ‖∑ w ∈ ({v} : Finset ι), u w‖ ^ 2) ≤ _ at h
    simpa [Real.sqrt_sq_eq_abs] using h
  exact (show T.Primal →ₗ[ℝ] ℝ from Finsupp.lapply v).mkContinuous 1 (by
      intro u
      change ‖(show ι →₀ ℝ from u) v‖ ≤ 1 * T.primalSeminorm u
      simpa only [one_mul, Real.norm_eq_abs] using coordinate_le_primal u v)

def coordinate (v : ι) : T.Dual :=
  (T.coordinateFinite v).extend UniformSpace.Completion.toComplL

/-- Primal unit coordinate and its canonical image in the completion. -/
def unitFinite (v : ι) : T.Primal := Finsupp.single v 1

def unitVector (v : ι) : T.JamesSpace := (T.unitFinite v : T.JamesSpace)

def headDual (H : Finset ι) : T.Dual →L[ℝ] T.Dual :=
  ∑ v ∈ H, (ContinuousLinearMap.apply ℝ ℝ (T.unitVector v)).smulRight (T.coordinate v)

/-- The norm-closed coordinate span, not the full infinite-tree dual. -/
def CoordinatePredual : Submodule ℝ T.Dual :=
  (Submodule.span ℝ (Set.range T.coordinate)).topologicalClosure

end SegmentSystem

/-- A finite interval in an ancestral order.  This keeps the root in every tree. -/
def intervalSystem {ι : Type*} (r : ι → ι → Prop)
    (hrefl : ∀ a, r a a) (hanti : ∀ a b, r a b → r b a → a = b) : SegmentSystem ι where
  IsSegment s := ∃ a b, r a b ∧ ∀ v, v ∈ s ↔ r a v ∧ r v b
  singleton v := by
    refine ⟨v, v, hrefl v, ?_⟩
    intro w
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨hrefl _, hrefl _⟩
    · intro h
      exact hanti w v h.2 h.1

/-- An ancestral partial order: the predecessors of any vertex form a chain. -/
class Ancestry (ι : Type*) extends PartialOrder ι where
  predecessors_total : ∀ {a b c : ι}, le a c → le b c → le a b ∨ le b a

namespace Ancestry

open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
local instance : PartialOrder ι := A.toPartialOrder

/-- Nonempty finite intervals for an ancestral order. -/
def segments : SegmentSystem ι :=
  intervalSystem (· ≤ ·) (fun _ => le_rfl) (fun _ _ => le_antisymm)

end Ancestry

def ForestNode := {hw : ℕ × List ℕ // 1 ≤ hw.1 ∧ hw.2.length ≤ hw.1}

def ForestAncestor (a b : ForestNode) : Prop :=
  a.val.1 = b.val.1 ∧ a.val.2.IsPrefix b.val.2

@[instance_reducible] def forestAncestry : Ancestry ForestNode where
  le := ForestAncestor
  lt a b := ForestAncestor a b ∧ ¬ ForestAncestor b a
  le_refl a := ⟨rfl, List.prefix_refl _⟩
  le_trans _ _ _ hab hbc := ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  le_antisymm a b hab hba := by
    apply Subtype.ext
    exact Prod.ext hab.1 (hab.2.sublist.antisymm hba.2.sublist)
  predecessors_total hab hac := by
    rcases List.prefix_or_prefix_of_prefix hab.2 hac.2 with h | h
    · exact Or.inl ⟨hab.1.trans hac.1.symm, h⟩
    · exact Or.inr ⟨hac.1.trans hab.1.symm, h⟩

def forestSegments : SegmentSystem ForestNode :=
  Ancestry.segments (A := forestAncestry)

/-- Prefix order on all finite words, explicitly distinct from their lexicographic order. -/
@[instance_reducible] def infiniteAncestry : Ancestry (List ℕ) where
  le := List.IsPrefix
  lt a b := a.IsPrefix b ∧ ¬ b.IsPrefix a
  le_refl := List.prefix_refl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm _ _ hab hba := hab.sublist.antisymm hba.sublist
  predecessors_total := List.prefix_or_prefix_of_prefix

/-- The infinite-height tree of all finite words; this includes the empty root. -/
def infiniteSegments : SegmentSystem (List ℕ) :=
  Ancestry.segments (A := infiniteAncestry)

abbrev ForestDual := forestSegments.Dual
abbrev InfinitePredual := infiniteSegments.CoordinatePredual

namespace Diamond

/-- Stage edges, retaining their parent, child number, and side. -/
@[reducible] def Edge : ℕ → Type
  | 0 => Unit
  | n + 1 => Edge n × ℕ × Bool

/-- At every replacement every parent edge receives countably many distinct new vertices. -/
@[reducible] def Vertex : ℕ → Type
  | 0 => Bool
  | n + 1 => Vertex n ⊕ (Edge n × ℕ)

def endpoint : (n : ℕ) → Edge n → Bool → Vertex n
  | 0, _, b => b
  | n + 1, (e, _, false), false => Sum.inl (endpoint n e false)
  | _ + 1, (e, i, false), true => Sum.inr (e, i)
  | _ + 1, (e, i, true), false => Sum.inr (e, i)
  | n + 1, (e, _, true), true => Sum.inl (endpoint n e true)

/-- The undirected replacement graph. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) :=
  SimpleGraph.fromRel (fun u v => ∃ e : Edge n, u = endpoint n e false ∧ v = endpoint n e true)

/-- Final edges have length 2⁻ᵏ: this is the shortest-path metric of the normalized graph. -/
def distance (k : ℕ) (u v : Vertex k) : ℝ :=
  ((graph k).dist u v : ℝ) / (Nat.cast 2 : ℝ) ^ k

end Diamond

def headline_all_pairs_statement : Prop :=
  (∀ (k : ℕ) (f : Diamond.Vertex k → ForestDual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2) ∧
    (∀ (k : ℕ) (f : Diamond.Vertex k → InfinitePredual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2)

end DiamondDistortion

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DiamondDistortion.headline_all_pairs_statement

end Problem

/- Formalization scope, from lean/docs/331.md: The paper constructs a Banach space whose midpoint geometry is asymptotically uniformly convex even though no equivalent norm is asymptotically uniformly convex in the usual one-sided sense. The formalization proves that the full dual of the specified segment-norm completion is infinite-dimensional, separable, and reflexive; its averaged midpoint modulus is at least $\sqrt{1+t^2/12}-1$ for every $t>0$, while every equivalent norm fails asymptotic uniform convexity. It also proves that an embedding of a depth-$k$ countably branching diamond has distortion at least $\sqrt{1+k/12}$. The general-forest and word-forest results use the closed span of the coordinate functionals. Their conclusions retain the finite-ancestor and equivalent-norm hypotheses, including the scale $\alpha/(2\beta)$ when $0<\alpha\le\beta$ and the new norm lies between $\alpha$ and $\beta$ times the original norm; they do not identify that span with the full dual or assert reflexivity for every forest. The paper controls midpoint lenses in Banach spaces defined by tree-segment norms. The formalization proves the following estimate in both the full dual of the finite-height forest space and the coordinate predual of the infinite-tree space. If $x$ is supported on a finite ancestral set $H$, $R\ge0$, and $\|x+y\|,\|x-y\|\le R$, then the part of $y$ outside $H$ has norm at most $2\sqrt{R^2-\|x\|^2}$. The formalization also covers selected consequences for averaged midpoint moduli and separated families of vectors, together with reflexivity and renorming obstructions. This scope concerns the segment-space results; the companion results on diamond energies remain separate. The paper studies embeddings of countably branching diamond graphs into Banach spaces built from tree segments. The formalization proves that every embedding of the depth-$k$ diamond with distortion $D$, at any positive scale, satisfies $1+k/4\le D^2$ in either of two spaces: the full dual of the completed finite-height forest space and the closed coordinate span in the dual of the infinite-tree space. The bound applies to all pairs of vertices and is unconditional. The formalization also contains selected graph deductions under explicit companion assumptions. Twenty-two of those companion inputs are assumed in these deductions; the diamond distortion bound above does not require them. The paper exhibits a real $L_1$ subspace with positive averaged midpoint convexity but no equivalent asymptotically uniformly convex norm. For every closed infinite-dimensional subspace whose unit ball is precompact in measure and which has the Daugavet property, the formalization computes the moduli at every unit vector: the averaged midpoint modulus is $\max(t/2,t-1)$ and the usual one-sided asymptotic modulus is $\max(0,t-2)$ for every $t>0$. The same formulas hold after taking the infimum over unit vectors, and every equivalent norm fails asymptotic uniform convexity. The formalization also constructs such a subspace on a countable product of unit intervals and proves that it has the stated measure-precompactness and Daugavet properties, so the modulus formulas apply to an actual example. The paper constructs Banach spaces from bounded tree potentials and path costs to separate averaged midpoint convexity from asymptotic uniform convexity. For the specified tree-potential completions, the formalization proves completeness, separability, infinite dimension, and an averaged midpoint modulus of at least $\sqrt{1+t^2/4}-1$ for $0<t<1$. No space linearly isomorphic to one of these completions is asymptotically uniformly convex. The formalization also covers selected path-cost duality and comparison results, clipping and energy estimates, and further renorming obstructions. These retain their stated support, head, and tail hypotheses; the remaining auxiliary assertions of the paper are outside this scope. The paper forms a real $L_1$ space from the closed span of products of independent multipliers along tree paths. For a positive, nonconstant multiplier of mean one and finite second moment, the formalization proves that this space is infinite-dimensional and has no equivalent asymptotically uniformly convex norm. For every $t>0$, the averaged midpoint modulus nevertheless has explicit positive lower bounds. If $G$ is a standard real Gaussian, the exponential-multiplier bound is $\frac{7t}{480}\mathbb E[(|G|-20/t)_+]$, where $u_+=\max(u,0)$. For squared-Gaussian multipliers, the bounds are $\frac18\Pr(|G|\ge4\sqrt2(2+\sqrt2)/t)$ and $\frac14\Pr(|G|\ge8\sqrt6/t)$. The paper constructs three Banach spaces from recursive tree potentials: a root-sum space, a zero-root space, and a joined space. The formalization proves that all three are infinite-dimensional and have no equivalent asymptotically uniformly convex norm. The root-sum and joined spaces have averaged midpoint modulus at least $t^3/128$ for $0<t<1$, and the root-sum modulus is positive for every $t>0$. The zero-root estimate retains its finite ancestral support and tail hypotheses, and the zero-root and joined spaces are reflexive. The formalization also covers a separated-midpoint result for the joined space and a variable-exponent model with its recursive norm, duality, projections, renorming obstruction, and sixth- and third-order stability estimates. The separation, sequence, support, and head assumptions in these results are essential parts of their statements. -/
