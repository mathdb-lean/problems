/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E423_refute
- collection: erdos
- question_id: erdos:423
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/423.lean#erdos_423
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Erdős Problem 423 [Er77c, p.71; ErGr80, p.83]: Let $a(1) = 1$, $a(2) = 2$, and for $k \ge 3$ let $a(k)$ be the least integer greater than $a(k-1)$ that is a sum of at least two consecutive terms of the sequence. What is the asymptotic behaviour of this sequence? It seems likely that $a_n = n + o(n)$.
- notes: Erdos Problem 423 -- https://www.erdosproblems.com/423
- track: open
- answer_shape: refute
- pair_id: E423
- pair_role: refute
- source_stem: 423
- mathdb_ref: erdos:423
- source_namespace: Erdos423
- source_theorem: erdos_423
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: IsHofstadterSeq.strictMono IsHofstadterSeq.le_apply IsHofstadterSeq.lt_iff_lt IsHofstadterSeq.infinite_compl_of_unbounded IsHofstadterSeq.unbounded_of_infinite_compl
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset BigOperators Filter Asymptotics

namespace Problem

/-- `IsConsecutiveBlockSum a k m` means that $m$ equals the sum of at least two
    consecutive terms of the sequence $a$, using indices from $\{1, \ldots, k - 1\}$.
    That is, there exist $i, j$ with $1 \le i$, $i + 1 \le j$, $j \le k - 1$ such that
    $m = a(i) + a(i+1) + \cdots + a(j)$. -/
def IsConsecutiveBlockSum (a : ℕ → ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
    m = ∑ l ∈ Finset.Icc i j, a l

/-- The Hofstadter sequence (OEIS A005243): $a(1) = 1$, $a(2) = 2$, and for $k \ge 3$,
$a(k)$ is the least integer $> a(k-1)$ that equals the sum of at least two consecutive terms from
$\{a(1), \ldots, a(k-1)\}$. The sequence begins $1, 2, 3, 5, 6, 8, 10, 11, \ldots$. -/
def IsHofstadterSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  ∀ k : ℕ, 3 ≤ k →
    IsConsecutiveBlockSum a k (a k) ∧
    a (k - 1) < a k ∧
    ∀ m : ℕ, a (k - 1) < m → m < a k → ¬IsConsecutiveBlockSum a k m

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- A Hofstadter sequence is strictly increasing from index `1` on. -/
@[category API, AMS 5 11]
theorem IsHofstadterSeq.strictMono {a : ℕ → ℕ} (ha : IsHofstadterSeq a) :
    StrictMono fun k => a (k + 1) := by
  obtain ⟨h1, h2, hk⟩ := ha
  refine strictMono_nat_of_lt_succ fun k => ?_
  show a (k + 1) < a (k + 1 + 1)
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · show a 1 < a 2
    omega
  · have := (hk (k + 2) (by omega)).2.1
    simpa using this

/-- A Hofstadter sequence satisfies `n ≤ a n` for `n ≥ 1`. -/
@[category API, AMS 5 11]
theorem IsHofstadterSeq.le_apply {a : ℕ → ℕ} (ha : IsHofstadterSeq a) (n : ℕ)
    (hn : 1 ≤ n) : n ≤ a n := by
  have h1 := ha.1
  induction n, hn using Nat.le_induction with
  | base => omega
  | succ k hk ih =>
    have := (IsHofstadterSeq.strictMono ha) (Nat.lt_succ_self (k - 1))
    simp only [show k - 1 + 1 = k by omega, show k - 1 + 1 + 1 = k + 1 by omega] at this
    omega

/-- For indices `≥ 1`, a Hofstadter sequence preserves and reflects `<`. -/
@[category API, AMS 5 11]
theorem IsHofstadterSeq.lt_iff_lt {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    a i < a j ↔ i < j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [(IsHofstadterSeq.strictMono ha).lt_iff_lt]
  omega

/-- If `a n - n` is unbounded, infinitely many integers are missed: when `a n ≥ N + 2 + n`,
the `n` values `a 0, …, a (n - 1)` cannot cover the `n + 1` integers in `[N + 1, a n - 1]`, and
later terms are too large. -/
@[category API, AMS 5 11]
theorem IsHofstadterSeq.infinite_compl_of_unbounded {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    (h : ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n) : Set.Infinite (Set.range a)ᶜ := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨n, hn⟩ := (h (N + 2)).exists_forall_of_atTop
  obtain ⟨n, hn1, hn⟩ : ∃ n, 1 ≤ n ∧ N + 2 + n ≤ a n :=
    ⟨max n 1, by omega, hn _ (le_max_left _ _)⟩
  -- The `n` values `a 0, …, a (n - 1)` cannot cover the `n + 1` integers in `[N + 1, a n - 1]`.
  have hcard : ((Finset.range n).image a).card < (Finset.Icc (N + 1) (a n - 1)).card := by
    calc ((Finset.range n).image a).card ≤ n := by
          simpa using Finset.card_image_le (s := Finset.range n) (f := a)
      _ < (Finset.Icc (N + 1) (a n - 1)).card := by simp; omega
  obtain ⟨x, hx, hxi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_Icc] at hx
  refine ⟨x, ?_, by omega⟩
  rintro ⟨k, rfl⟩
  rcases Nat.lt_or_ge k n with hk | hk
  · exact hxi (Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, rfl⟩)
  · have : a n ≤ a k := by
      rcases eq_or_lt_of_le hk with rfl | hk'
      · exact le_rfl
      · exact ((IsHofstadterSeq.lt_iff_lt ha hn1 (by omega)).2 hk').le
    omega

/-- If infinitely many integers are missed, `a n - n` is unbounded: `M + 1` missed integers
below `n` together with `a 1, …, a n` are distinct elements of `[1, a n]`. -/
@[category API, AMS 5 11]
theorem IsHofstadterSeq.unbounded_of_infinite_compl {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    (h : Set.Infinite (Set.range a)ᶜ) : ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n := by
  intro M
  obtain ⟨t, hts, htc⟩ := h.exists_subset_card_eq (M + 1)
  -- All missed values in `t` are at most `X`.
  set X := t.sup id with hX
  rw [Filter.eventually_atTop]
  refine ⟨X + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  -- `a 1, …, a n` and the positive elements of `t` are distinct integers in `[1, a n]`.
  set A := (Finset.Icc 1 n).image a with hA
  set T := t.filter (fun x => 1 ≤ x) with hT
  have hAcard : A.card = n := by
    rw [hA, Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro i hi j hj hij
      rw [Finset.coe_Icc, Set.mem_Icc] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd hij ((IsHofstadterSeq.lt_iff_lt ha hi.1 hj.1).2 hlt).ne
      · exact absurd hij.symm ((IsHofstadterSeq.lt_iff_lt ha hj.1 hi.1).2 hlt).ne
  have hTcard : M ≤ T.card := by
    have : (t.filter (fun x => ¬ 1 ≤ x)).card ≤ 1 := by
      calc (t.filter (fun x => ¬ 1 ≤ x)).card ≤ ({0} : Finset ℕ).card :=
            Finset.card_le_card fun x hx => by
              rw [Finset.mem_filter] at hx; simp; omega
        _ = 1 := rfl
    have := Finset.card_filter_add_card_filter_not (s := t) (fun x => 1 ≤ x)
    rw [← hT] at this
    omega
  have hdisj : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro x hxA hxT
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hxA
    exact hts (Finset.mem_filter.1 hxT).1 ⟨k, rfl⟩
  have hsub : A ∪ T ⊆ Finset.Icc 1 (a n) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rw [Finset.mem_Icc]
    rcases hx with hx | hx
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_Icc] at hk
      refine ⟨IsHofstadterSeq.le_apply ha k hk.1 |>.trans' (by omega), ?_⟩
      rcases eq_or_lt_of_le hk.2 with rfl | hlt
      · exact le_rfl
      · exact ((IsHofstadterSeq.lt_iff_lt ha hk.1 hn1).2 hlt).le
    · obtain ⟨hxt, hx1⟩ := Finset.mem_filter.1 hx
      have : x ≤ X := Finset.le_sup (f := id) hxt
      exact ⟨hx1, by have := IsHofstadterSeq.le_apply ha n hn1; omega⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hAcard, Nat.card_Icc] at this
  omega

abbrev Target : Prop :=
    ¬ (
      ∀ a : ℕ → ℕ, IsHofstadterSeq a →
          (fun n : ℕ => (a n : ℝ) - n) =o[atTop] (fun n : ℕ => (n : ℝ))
    )

end Problem
