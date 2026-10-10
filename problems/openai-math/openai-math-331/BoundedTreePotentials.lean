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

- problem_id: BoundedTreePotentials
- collection: openai-math
- question_id: openai-math:331
- source: openai-math
- source_locator: lean/ComparatorChallenges/BoundedTreePotentials.lean#OAI.BoundedTreePotentials.TreeCalculus.main_counterexample
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a real reflexive Banach space with an asymptotically midpoint uniformly convex norm but no equivalent asymptotically uniformly convex norm, extending Baudier's separation to reflexive spaces. In the same space, depth-k countably branching diamonds require distortion at least $`\sqrt{1+k/12}`$, so midpoint uniform convexity does not force uniformly bounded diamond distortion even under reflexivity. ([Lean](lean/docs/331.md)) We construct a separable reflexive real Banach space whose given norm is asymptotically midpoint uniformly convex but which admits no asymptotically uniformly convex equivalent norm. Its averaged midpoint modulus is at least $`\sqrt{1+t^2/12}-1`$, and the countably branching diamond of depth k has distortion at least $`\sqrt{1+k/12}`$ in this space. This gives a negative answer to the reflexive diamond converse for asymptotic uniform convexifiability. For a real segment-forest dual with unbounded finite component heights and the real infinite-height coordinate predual, we bound the tail of an arbitrary displacement in a symmetric lens by $`2\sqrt{R^2-\|x\|^2}`$, where R is the lens radius and x is its finitely supported center. Both given norms are asymptotically midpoint uniformly convex, although neither space admits an equivalent asymptotically uniformly convex norm. The finite-height forest dual is reflexive. We derive quantitative distortion bounds for countably branching diamond graphs from midpoint estimates and direct tree energies. In the dual of a finite-height segment forest, every distortion-D embedding of the depth-k diamond satisfies $`D^2\ge1+k/4`$. The same bound holds in the infinite-height coordinate predual. We also obtain power-type distortion bounds for path-cost and recursive tree norms. For an infinite-dimensional real subspace of L1 whose unit ball is totally bounded in measure and whose norm has the Daugavet property, we compute the averaged midpoint and one-sided asymptotic moduli at every unit center. They are $`\max\{t/2,t-1\}`$ and $`\max\{0,t-2\}`$, respectively. The same weak-neighborhood geometry excludes every equivalent asymptotically uniformly convex norm. A quantitative realization of the Kadets–Werner construction supplies a space with both hypotheses. Four real Banach spaces defined by bounded tree potentials satisfy the averaged asymptotic midpoint bound $`\widehat\delta(t)\ge\sqrt{1+t^2/4}-1`$ for $`0\lt t\lt 1`$, while none admits an asymptotically uniformly convex (AUC) renorming. On finite-height trees, the globally constrained norm equals the least additive cost of a Hilbert vector and root paths. The quadratic path and segment-start outer Hilbert sums are reflexive and asymptotically midpoint uniformly convex, and admit no equivalent AUC norm. For a countably branching tree, the closed real L1 spans of products of independent exponential or Gaussian-square multipliers along its paths have positive averaged asymptotic midpoint moduli and admit no equivalent asymptotically uniformly convex norm. The renorming obstruction holds for every positive nonconstant mean-one multiplier with finite second moment. We study tree norms computed by two least nonnegative fields whose difference is the vector. For Euclidean child aggregation, two root-sum spaces have an averaged asymptotic midpoint modulus of at least $`t^3/128`$ for $`0\lt t\lt 1`$, including a reflexive joining-root space. A reflexive construction with a fixed zero root also satisfies a homogeneous cubic estimate. These spaces admit no equivalent asymptotically uniformly convex norm. We also obtain sixth-power and cubic estimates when the aggregation exponent depends on the height of a finite component.
- notes: OpenAI math result family 331, Reflexive midpoint convexity and diamond distortion -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/331.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.BoundedTreePotentials.TreeCalculus.main_counterexample
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.TreePotential.Main
- source_main_result: OAI.BoundedTreePotentials.TreeCalculus.main_counterexample
- source_papers: preprints/Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026/manuscript.pdf preprints/Midpoint-lenses-in-segment-spaces-September-27-2026/manuscript.pdf preprints/Diamond-distortion-from-midpoint-and-tree-energies-September-27-2026/manuscript.pdf preprints/Exact-asymptotic-moduli-in-a-Daugavet-subspace-of-L1-September-27-2026/manuscript.pdf preprints/Midpoint-convexity-from-bounded-tree-potentials-and-path-costs-September-27-2026/manuscript.pdf preprints/Independent-products-in-real-L1-asymptotic-midpoint-convexity-without-AUC-renormings-September-27-2026/manuscript.pdf preprints/Midpoint-convexity-from-two-recursive-potentials-September-27-2026/manuscript.pdf
- source_scope_note: lean/docs/331.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

universe u
open Set
open scoped ENNReal Classical

namespace BoundedTreePotentials

section TestNorms

variable {I : Type*}

structure TestFamily (I : Type*) where
  carrier : Set (I → ℝ)
  zero_mem : (0 : I → ℝ) ∈ carrier
  neg_mem : ∀ f ∈ carrier, -f ∈ carrier
  coeff_bound : ∀ f ∈ carrier, ∀ i, |f i| ≤ 1
  singleton_mem : ∀ i, (fun j => if j = i then (1 : ℝ) else 0) ∈ carrier

instance : CoeSort (TestFamily I) (Type _) := ⟨fun K => K.carrier⟩
instance (K : TestFamily I) : Nonempty K.carrier := ⟨⟨0, K.zero_mem⟩⟩

def finitePairing (f : I → ℝ) : (I →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ f

def testNorm (K : TestFamily I) (x : I →₀ ℝ) : ℝ :=
  ⨆ f : K, |finitePairing f.val x|

def testSeminorm (K : TestFamily I) : Seminorm ℝ (I →₀ ℝ) := by
  have finitePairing_apply (f : I → ℝ) (x : I →₀ ℝ) :
      finitePairing f x = ∑ i ∈ x.support, x i * f i := rfl
  have finitePairing_abs_bound (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ ∑ i ∈ x.support, |x i| := by
    rw [finitePairing_apply]
    calc
      |∑ i ∈ x.support, x i * f.val i| ≤ ∑ i ∈ x.support, |x i * f.val i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ x.support, |x i| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (K.coeff_bound _ f.property i)
  have testNorm_bddAbove (K : TestFamily I) (x : I →₀ ℝ) :
      BddAbove (range fun f : K => |finitePairing f.val x|) :=
    ⟨∑ i ∈ x.support, |x i|, by rintro _ ⟨f, rfl⟩; exact finitePairing_abs_bound K f x⟩
  have finitePairing_le_testNorm (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ testNorm K x := le_ciSup (testNorm_bddAbove K x) f
  have testNorm_nonneg (K : TestFamily I) (x : I →₀ ℝ) : 0 ≤ testNorm K x :=
    (abs_nonneg _).trans (finitePairing_le_testNorm K ⟨0, K.zero_mem⟩ x)
  have testNorm_le_l1 (K : TestFamily I) (x : I →₀ ℝ) :
      testNorm K x ≤ ∑ i ∈ x.support, |x i| := by
    apply ciSup_le
    exact fun f => finitePairing_abs_bound K f x
  have testNorm_zero (K : TestFamily I) : testNorm K 0 = 0 := by
    apply le_antisymm
    · simpa using testNorm_le_l1 K 0
    · exact testNorm_nonneg K 0
  have testNorm_add_le (K : TestFamily I) (x y : I →₀ ℝ) :
      testNorm K (x + y) ≤ testNorm K x + testNorm K y := by
    apply ciSup_le
    intro f
    rw [map_add]
    exact (abs_add_le _ _).trans (add_le_add
      (finitePairing_le_testNorm K f x) (finitePairing_le_testNorm K f y))
  have testNorm_smul_le (K : TestFamily I) (a : ℝ) (x : I →₀ ℝ) :
      testNorm K (a • x) ≤ ‖a‖ * testNorm K x := by
    apply ciSup_le
    intro f
    rw [map_smul, smul_eq_mul, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (finitePairing_le_testNorm K f x) (abs_nonneg a)
  exact Seminorm.ofSMulLE (testNorm K) (testNorm_zero K) (testNorm_add_le K) (testNorm_smul_le K)

def TestVector (_ : TestFamily I) := I →₀ ℝ

instance (K : TestFamily I) : AddCommGroup (TestVector K) := inferInstanceAs (AddCommGroup (I →₀ ℝ))
instance (K : TestFamily I) : Module ℝ (TestVector K) := inferInstanceAs (Module ℝ (I →₀ ℝ))
instance (K : TestFamily I) : Norm (TestVector K) := ⟨testNorm K⟩

instance (K : TestFamily I) : NormedAddCommGroup (TestVector K) := by
  have finitePairing_apply (f : I → ℝ) (x : I →₀ ℝ) :
      finitePairing f x = ∑ i ∈ x.support, x i * f i := rfl
  have finitePairing_abs_bound (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ ∑ i ∈ x.support, |x i| := by
    rw [finitePairing_apply]
    calc
      |∑ i ∈ x.support, x i * f.val i| ≤ ∑ i ∈ x.support, |x i * f.val i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ x.support, |x i| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (K.coeff_bound _ f.property i)
  have testNorm_bddAbove (K : TestFamily I) (x : I →₀ ℝ) :
      BddAbove (range fun f : K => |finitePairing f.val x|) :=
    ⟨∑ i ∈ x.support, |x i|, by rintro _ ⟨f, rfl⟩; exact finitePairing_abs_bound K f x⟩
  have finitePairing_le_testNorm (K : TestFamily I) (f : K) (x : I →₀ ℝ) :
      |finitePairing f.val x| ≤ testNorm K x := le_ciSup (testNorm_bddAbove K x) f
  have finitePairing_single_test (x : I →₀ ℝ) (i : I) :
      finitePairing (fun j => if j = i then (1 : ℝ) else 0) x = x i := by
    classical
    rw [finitePairing_apply]
    simp only [mul_ite, mul_one, mul_zero]
    by_cases hi : i ∈ x.support
    · simp [hi]
    · simp [hi, Finsupp.notMem_support_iff.mp hi]
  have coordinate_le_testNorm (K : TestFamily I) (x : I →₀ ℝ) (i : I) :
      |x i| ≤ testNorm K x := by
    convert finitePairing_le_testNorm K ⟨_, K.singleton_mem i⟩ x using 1
    rw [finitePairing_single_test]
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    norm_nonneg := apply_nonneg (testSeminorm K)
    norm_smul := map_smul_eq_mul (testSeminorm K)
    norm_triangle := map_add_le_add (testSeminorm K)
    norm_eq_zero_iff := fun x => ⟨by
      intro h
      apply Finsupp.ext
      intro i
      exact abs_nonpos_iff.mp (h ▸ coordinate_le_testNorm K x i), by
      rintro rfl
      exact map_zero (testSeminorm K)⟩ }

instance (K : TestFamily I) : NormedSpace ℝ (TestVector K) where
  norm_smul_le a x := le_of_eq (map_smul_eq_mul (testSeminorm K) a x)

abbrev TestCompletion (K : TestFamily I) := UniformSpace.Completion (TestVector K)

end TestNorms

namespace TreeCalculus

abbrev Node := List ℕ

def potential (f : Node → ℝ) (s : Node) : ℝ := (s.inits.map f).sum

inductive QuadraticKind where
  | sibling | antichain | global
  deriving DecidableEq

def QuadraticGroup : QuadraticKind → Finset Node → Prop
  | .sibling, B => ∃ r, ∀ s ∈ B, ∃ j, s = r ++ [j]
  | .antichain, B => (B : Set Node).Pairwise (fun s t => ¬s <+: t ∧ ¬t <+: s)
  | .global, _ => True

def QuadraticBudget (k : QuadraticKind) (f : Node → ℝ) : Prop :=
  ∀ B : Finset Node, QuadraticGroup k B → ∑ s ∈ B, f s ^ 2 ≤ 1

def CoefficientSupport : QuadraticKind → (Node → ℝ) → Prop
  | .sibling, _ => True
  | .antichain, f => (Function.support f).Finite
  | .global, f => Memℓp f 2

structure IsTreeTest (includeRoot : Bool) (k : QuadraticKind) (f : Node → ℝ) : Prop where
  root_zero : includeRoot = false → f [] = 0
  potential_bound : ∀ s, |potential f s| ≤ 1
  quadratic_budget : QuadraticBudget k f
  coefficient_support : CoefficientSupport k f

abbrev TreeCoordinate (includeRoot : Bool) := {s : Node // includeRoot = true ∨ s ≠ []}

def liftCoefficients (r : Bool) (f : TreeCoordinate r → ℝ) (s : Node) : ℝ :=
  if h : r = true ∨ s ≠ [] then f ⟨s, h⟩ else 0

def treeTestFamily (r : Bool) (k : QuadraticKind) : TestFamily (TreeCoordinate r) := by
  have potential_root (f : Node → ℝ) : potential f [] = f [] := by simp [potential]
  have potential_child (f : Node → ℝ) (s : Node) (j : ℕ) :
      potential f (s ++ [j]) = potential f s + f (s ++ [j]) := by
    simp [potential, List.inits_append]
  have potential_smul (a : ℝ) (f : Node → ℝ) (s : Node) :
      potential (a • f) s = a * potential f s := by
    induction s using List.reverseRecOn with
    | nil => simp [potential_root]
    | append_singleton s j ih => simp only [potential_child, ih, Pi.smul_apply, smul_eq_mul]; ring
  have quadratic_singleton (k : QuadraticKind) {s : Node} (hs : s ≠ []) :
      QuadraticGroup k {s} := by
    cases k with
    | sibling =>
      cases s using List.reverseRecOn with
      | nil => exact (hs rfl).elim
      | append_singleton s j =>
        refine ⟨s, ?_⟩
        intro t ht
        have ht' : t = s ++ [j] := by simpa using ht
        exact ⟨j, ht'⟩
    | antichain => simp [QuadraticGroup]
    | global => trivial
  have test_coefficient_bound {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
      (hf : IsTreeTest r k f) (s : Node) : |f s| ≤ 1 := by
    by_cases hs : s = []
    · subst s; simpa only [potential_root] using hf.potential_bound []
    · have h := hf.quadratic_budget {s} (quadratic_singleton k hs)
      rw [Finset.sum_singleton] at h
      exact (sq_le_one_iff_abs_le_one (f s)).mp h
  have quadraticBudget_dominate {k : QuadraticKind} {f g : Node → ℝ}
      (hf : QuadraticBudget k f) (h : ∀ s, |g s| ≤ |f s|) : QuadraticBudget k g := by
    intro B hB
    apply le_trans _ (hf B hB)
    apply Finset.sum_le_sum
    intro s hs
    exact (sq_le_sq).mpr (h s)
  have coefficientSupport_dominate {k : QuadraticKind} {f g : Node → ℝ}
      (hf : CoefficientSupport k f) (h : ∀ s, |g s| ≤ |f s|) : CoefficientSupport k g := by
    cases k with
    | sibling => trivial
    | antichain =>
      apply hf.subset
      intro s hs
      change g s ≠ 0 at hs
      change f s ≠ 0
      intro hzero
      have hh := h s
      rw [hzero, abs_zero] at hh
      exact hs (abs_nonpos_iff.mp hh)
    | global =>
      exact (hf.norm).mono (by intro s; simpa only [Real.norm_eq_abs] using h s)
  have zero_isTreeTest (r : Bool) (k : QuadraticKind) : IsTreeTest r k 0 := by
    constructor
    · simp
    · intro s
      change |(s.inits.map fun _ => (0 : ℝ)).sum| ≤ 1
      simp
    · intro B hB; simp
    · cases k with
      | sibling => trivial
      | antichain => simp [CoefficientSupport]
      | global => exact zero_memℓp
  have neg_isTreeTest {r : Bool} {k : QuadraticKind} {f : Node → ℝ}
      (hf : IsTreeTest r k f) : IsTreeTest r k (-f) := by
    constructor
    · intro hr; simpa using congrArg Neg.neg (hf.root_zero hr)
    · intro s
      have he : -f = (-1 : ℝ) • f := by ext s; simp
      rw [he, potential_smul, neg_one_mul, abs_neg]
      exact hf.potential_bound s
    · exact quadraticBudget_dominate hf.quadratic_budget (by intro s; simp)
    · exact coefficientSupport_dominate hf.coefficient_support (by intro s; simp)
  have inits_nodup (s : Node) : s.inits.Nodup := by
    induction s using List.reverseRecOn with
    | nil => simp
    | append_singleton s j ih =>
      have he : (s ++ [j]).inits = s.inits ++ [s ++ [j]] := by simp [List.inits_append]
      rw [he, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb hab
      have hb' : b = s ++ [j] := by simpa using hb
      have hp := ((List.mem_inits a s).mp ha).length_le
      rw [hab, hb', List.length_append, List.length_singleton] at hp
      exact Nat.not_succ_le_self _ hp
  have potential_single (i s : Node) :
      potential (Pi.single i (1 : ℝ)) s = if i <+: s then 1 else 0 := by
    rw [potential, ← List.sum_toFinset _ (inits_nodup s)]
    simp only [Pi.single_apply]
    by_cases h : i <+: s
    · have hm : i ∈ s.inits.toFinset := List.mem_toFinset.mpr ((List.mem_inits i s).mpr h)
      simp [hm, h]
    · have hm : i ∉ s.inits.toFinset := fun hm => h ((List.mem_inits i s).mp (List.mem_toFinset.mp hm))
      simp [hm, h]
  have single_isTreeTest (r : Bool) (k : QuadraticKind) {i : Node}
      (hi : r = true ∨ i ≠ []) : IsTreeTest r k (Pi.single i (1 : ℝ)) := by
    constructor
    · intro hr
      have hn : [] ≠ i := by
        rcases hi with hi | hi
        · simp_all
        · exact Ne.symm hi
      exact Pi.single_eq_of_ne hn _
    · intro s
      rw [potential_single]
      split_ifs <;> norm_num
    · intro B hB
      simp only [Pi.single_apply, ite_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      by_cases h : i ∈ B <;> simp [h]
    · cases k with
      | sibling => trivial
      | antichain =>
        change (Function.support (Pi.single i (1 : ℝ))).Finite
        exact (Set.finite_singleton i).subset (by intro s hs; simpa [Function.mem_support, Pi.single_apply] using hs)
      | global => exact (lp.single (E := fun _ : Node => ℝ) 2 i (1 : ℝ)).property
  have liftCoefficients_coord {r : Bool} (f : TreeCoordinate r → ℝ) (s : TreeCoordinate r) :
      liftCoefficients r f s.val = f s := by simp [liftCoefficients, s.property]
  have liftCoefficients_zero (r : Bool) : liftCoefficients r 0 = 0 := by
    ext s; simp [liftCoefficients]
  have liftCoefficients_neg (r : Bool) (f : TreeCoordinate r → ℝ) :
      liftCoefficients r (-f) = -liftCoefficients r f := by
    ext s
    by_cases h : r = true ∨ s ≠ [] <;> simp [liftCoefficients, h]
  exact {
    carrier := {f | IsTreeTest r k (liftCoefficients r f)}
    zero_mem := by
      change IsTreeTest r k (liftCoefficients r 0)
      rw [liftCoefficients_zero]
      exact zero_isTreeTest r k
    neg_mem := by
      intro f hf
      change IsTreeTest r k (liftCoefficients r (-f))
      rw [liftCoefficients_neg]
      exact neg_isTreeTest hf
    coeff_bound := by
      intro f hf i
      simpa only [liftCoefficients_coord] using test_coefficient_bound hf i.val
    singleton_mem := by
      rintro ⟨i, hi⟩
      change IsTreeTest r k (liftCoefficients r _)
      convert single_isTreeTest r k hi using 1
      ext s
      by_cases h : r = true ∨ s ≠ []
      · simp [liftCoefficients, h, Pi.single_apply, Subtype.mk.injEq]
      · have hn : s ≠ i := by rintro rfl; exact h hi
        simp [liftCoefficients, h, hn] }

end TreeCalculus

section AsymptoticModuli

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure ClosedFiniteCodim where
  space : Submodule ℝ E
  closed : IsClosed (space : Set E)
  finiteCodim : Module.Finite ℝ (E ⧸ space)

def averagedModulusReal (t : ℝ) : ℝ :=
  ⨅ x : {x : E // ‖x‖=1},⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ 1≤‖y‖},
      (‖x.val+t • y.val‖+‖x.val-t • y.val‖)/((2 : ℕ) : ℝ)-1

def oneSidedModulusReal (t : ℝ) : ℝ :=
  ⨅ x : {x : E // ‖x‖=1},⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ ‖y‖=1},‖x.val+t • y.val‖-1

def IsAUCReal : Prop := ∀ t : ℝ, 0 < t → 0 < oneSidedModulusReal E t

end AsymptoticModuli

open TreeCalculus in
def TreeCalculus.main_counterexample_statement : Prop :=
  ∀ (r : Bool) (k : QuadraticKind),
    (CompleteSpace (TestCompletion (treeTestFamily r k)) ∧
      TopologicalSpace.SeparableSpace (TestCompletion (treeTestFamily r k)) ∧
      ¬Module.Finite ℝ (TestCompletion (treeTestFamily r k))) ∧
    (∀ t : ℝ, 0 < t → t < 1 →
      Real.sqrt (1 + t ^ 2 / 4) - 1 ≤
        averagedModulusReal (TestCompletion (treeTestFamily r k)) t) ∧
    (∀ (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℝ Y],
      (TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) → ¬IsAUCReal Y)

end BoundedTreePotentials

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.BoundedTreePotentials.TreeCalculus.main_counterexample_statement.{u}

end Problem

/- Formalization scope, from lean/docs/331.md: The paper constructs a Banach space whose midpoint geometry is asymptotically uniformly convex even though no equivalent norm is asymptotically uniformly convex in the usual one-sided sense. The formalization proves that the full dual of the specified segment-norm completion is infinite-dimensional, separable, and reflexive; its averaged midpoint modulus is at least $\sqrt{1+t^2/12}-1$ for every $t>0$, while every equivalent norm fails asymptotic uniform convexity. It also proves that an embedding of a depth-$k$ countably branching diamond has distortion at least $\sqrt{1+k/12}$. The general-forest and word-forest results use the closed span of the coordinate functionals. Their conclusions retain the finite-ancestor and equivalent-norm hypotheses, including the scale $\alpha/(2\beta)$ when $0<\alpha\le\beta$ and the new norm lies between $\alpha$ and $\beta$ times the original norm; they do not identify that span with the full dual or assert reflexivity for every forest. The paper controls midpoint lenses in Banach spaces defined by tree-segment norms. The formalization proves the following estimate in both the full dual of the finite-height forest space and the coordinate predual of the infinite-tree space. If $x$ is supported on a finite ancestral set $H$, $R\ge0$, and $\|x+y\|,\|x-y\|\le R$, then the part of $y$ outside $H$ has norm at most $2\sqrt{R^2-\|x\|^2}$. The formalization also covers selected consequences for averaged midpoint moduli and separated families of vectors, together with reflexivity and renorming obstructions. This scope concerns the segment-space results; the companion results on diamond energies remain separate. The paper studies embeddings of countably branching diamond graphs into Banach spaces built from tree segments. The formalization proves that every embedding of the depth-$k$ diamond with distortion $D$, at any positive scale, satisfies $1+k/4\le D^2$ in either of two spaces: the full dual of the completed finite-height forest space and the closed coordinate span in the dual of the infinite-tree space. The bound applies to all pairs of vertices and is unconditional. The formalization also contains selected graph deductions under explicit companion assumptions. Twenty-two of those companion inputs are assumed in these deductions; the diamond distortion bound above does not require them. The paper exhibits a real $L_1$ subspace with positive averaged midpoint convexity but no equivalent asymptotically uniformly convex norm. For every closed infinite-dimensional subspace whose unit ball is precompact in measure and which has the Daugavet property, the formalization computes the moduli at every unit vector: the averaged midpoint modulus is $\max(t/2,t-1)$ and the usual one-sided asymptotic modulus is $\max(0,t-2)$ for every $t>0$. The same formulas hold after taking the infimum over unit vectors, and every equivalent norm fails asymptotic uniform convexity. The formalization also constructs such a subspace on a countable product of unit intervals and proves that it has the stated measure-precompactness and Daugavet properties, so the modulus formulas apply to an actual example. The paper constructs Banach spaces from bounded tree potentials and path costs to separate averaged midpoint convexity from asymptotic uniform convexity. For the specified tree-potential completions, the formalization proves completeness, separability, infinite dimension, and an averaged midpoint modulus of at least $\sqrt{1+t^2/4}-1$ for $0<t<1$. No space linearly isomorphic to one of these completions is asymptotically uniformly convex. The formalization also covers selected path-cost duality and comparison results, clipping and energy estimates, and further renorming obstructions. These retain their stated support, head, and tail hypotheses; the remaining auxiliary assertions of the paper are outside this scope. The paper forms a real $L_1$ space from the closed span of products of independent multipliers along tree paths. For a positive, nonconstant multiplier of mean one and finite second moment, the formalization proves that this space is infinite-dimensional and has no equivalent asymptotically uniformly convex norm. For every $t>0$, the averaged midpoint modulus nevertheless has explicit positive lower bounds. If $G$ is a standard real Gaussian, the exponential-multiplier bound is $\frac{7t}{480}\mathbb E[(|G|-20/t)_+]$, where $u_+=\max(u,0)$. For squared-Gaussian multipliers, the bounds are $\frac18\Pr(|G|\ge4\sqrt2(2+\sqrt2)/t)$ and $\frac14\Pr(|G|\ge8\sqrt6/t)$. The paper constructs three Banach spaces from recursive tree potentials: a root-sum space, a zero-root space, and a joined space. The formalization proves that all three are infinite-dimensional and have no equivalent asymptotically uniformly convex norm. The root-sum and joined spaces have averaged midpoint modulus at least $t^3/128$ for $0<t<1$, and the root-sum modulus is positive for every $t>0$. The zero-root estimate retains its finite ancestral support and tail hypotheses, and the zero-root and joined spaces are reflexive. The formalization also covers a separated-midpoint result for the joined space and a variable-exponent model with its recursive norm, duality, projections, renorming obstruction, and sixth- and third-order stability estimates. The separation, sequence, support, and head assumptions in these results are essential parts of their statements. -/
