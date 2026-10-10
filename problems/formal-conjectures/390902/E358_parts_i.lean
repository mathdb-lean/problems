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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E358_parts_i
- collection: erdos
- question_id: erdos:358
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/358.lean#erdos_358.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A=\{a_1 < \cdots\}$ be an infinite sequence of integers. Let $f(n)$ count the number of solutions to $$n=\sum_{u\leq i\leq v}a_i.$$ Is there such an $A$ for which $f(n)\to \infty$ as $n\to \infty$? Tao [Ta26] constructed such a sequence with $f(n) \gg \log n$ for all sufficiently large $n$.
- notes: Erdos Problem 358 -- https://www.erdosproblems.com/358
- track: solved
- answer_shape: decide
- source_stem: 358
- mathdb_ref: erdos:358
- source_namespace: Erdos358
- source_theorem: erdos_358.parts.i
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: one_le_g_of_two_le_f
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Filter Finset

/-
Let $a$ be an infinite sequence of integers. `intervalRepresentations A n` is the set of solutions
to $$n=\sum_{u\leq i\leq v}a_i.$$ where `u` and `v` are positive integers.
-/
def intervalRepresentations (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, A i}

/-
Let $a$ be an infinite sequence of integers. Let $f(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$
-/
noncomputable def f (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentations A n)

/-
Let $a$ be an infinite sequence of integers. `intervalRepresentationsNonTrivial A n` is the set of
solutions to $$n=\sum_{u\leq i\leq v}a_i$$ such that the sum has at least two terms.
-/
def intervalRepresentationsNonTrivial (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ u < v ∧ n = ∑ i ∈ Icc u v, A i}

/-
Let $a$ be an infinite sequence of integers. Let $g(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$ such that the sum has at least two terms.
-/
noncomputable def g (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentationsNonTrivial A n)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
If $A$ is strictly increasing then any $n > 0$ has at most one representation
$$n=\sum_{u\leq i\leq v}a_i$$ with a single term, so discarding the single-term representations
loses at most one solution.
-/
@[category API, AMS 5 11]
theorem one_le_g_of_two_le_f {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n)
    (hf : 2 ≤ f A n) : 1 ≤ g A n := by
  classical
  have hfin : (intervalRepresentations A n).Finite := by
    rcases Set.finite_or_infinite (intervalRepresentations A n) with h | h
    · exact h
    · rw [f, @Nat.card_eq_zero_of_infinite _ h.to_subtype] at hf
      omega
  have hsub : intervalRepresentationsNonTrivial A n ⊆ intervalRepresentations A n := by
    rintro ⟨u, v⟩ hr
    simp only [intervalRepresentationsNonTrivial, Set.mem_ofPred_eq] at hr
    simp only [intervalRepresentations, Set.mem_ofPred_eq]
    exact ⟨hr.1, hr.2.1, hr.2.2.2⟩
  refine (Set.ncard_pos (hfin.subset hsub)).mpr ?_
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  -- Without a representation of length at least two, every representation is a single term.
  have key : ∀ r ∈ intervalRepresentations A n, r.1 = r.2 ∧ A r.1 = n := by
    rintro ⟨u, v⟩ hr
    simp only [intervalRepresentations, Set.mem_ofPred_eq] at hr
    obtain ⟨hu, hv, hsum⟩ := hr
    have hle : u ≤ v := by
      by_contra hc
      rw [Finset.Icc_eq_empty hc, Finset.sum_empty] at hsum
      omega
    have huv : u = v := by
      rcases eq_or_lt_of_le hle with h | h
      · exact h
      · exact absurd (Set.eq_empty_iff_forall_notMem.mp hempty (u, v)
          (by simp only [intervalRepresentationsNonTrivial, Set.mem_ofPred_eq]
              exact ⟨hu, hv, h, hsum⟩)) (by simp)
    subst huv
    exact ⟨rfl, by simpa using hsum.symm⟩
  -- Injectivity of `A` then makes that single term unique, contradicting `2 ≤ f A n`.
  have := hfin.to_subtype
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.one_lt_ncard_iff_nontrivial.mp hf
  obtain ⟨hp₁, hpn⟩ := key p hp
  obtain ⟨hq₁, hqn⟩ := key q hq
  exact hpq (Prod.ext (hA.injective (hpn.trans hqn.symm))
    (by rw [← hp₁, ← hq₁]; exact hA.injective (hpn.trans hqn.symm)))

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ A, StrictMono A ∧ atTop.Tendsto (f A) atTop

end Problem
