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

- problem_id: E56
- collection: erdos
- question_id: erdos:56
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/56.lean#erdos_56
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose $A \subseteq \{1,\dots,N\}$ is such that there are no $k+1$ elements of $A$ which are relatively prime. An example is the set of all multiples of the first $k$ primes. Is this the largest such set? To avoid trivial counterexamples, we must insist that $N$ be at least the $k$th prime.
- notes: Erdos Problem 56 -- https://www.erdosproblems.com/56
- track: solved
- answer_shape: decide
- source_stem: 56
- mathdb_ref: erdos:56
- source_namespace: Erdos56
- source_theorem: erdos_56
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: weaklyDivisible_empty weaklyDivisible_singleton not_weaklyDivisible_zero empty_iff_weaklyDivisible_zero maxWeaklyDivisible_zero maxWeaklyDivisible_one maxWeaklyDivisible_zero_k firstPrimesMultiples_one_card_zero firstPrimesMultiples_zero_k_card_zero weaklyDivisible_firstPrimesMultiples
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open scoped Finset

namespace Problem

/--
Say a set of natural numbers is `k`-weakly divisible if any `k+1` elements
of `A` are not relatively prime.
-/
def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
    ∀ s ∈ A.powersetCard (k + 1), ¬ Set.Pairwise s Nat.Coprime

/--
`MaxWeaklyDivisible N k` is the size of the largest k-weakly divisible subset of `{1,..., N}`
-/
noncomputable def MaxWeaklyDivisible (N : ℕ) (k : ℕ) : ℕ :=
  sSup {#A | (A : Finset ℕ) (_ : A ⊆ Finset.Icc 1 N) (_ : WeaklyDivisible k A)}

/--
`FirstPrimesMultiples N k` is the set of numbers in `{1,..., N}` that are
a multiple of one of the first `k` primes.
-/
noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
    (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category API, AMS 11]
lemma weaklyDivisible_empty (k : ℕ): WeaklyDivisible k {} := by
  simp [WeaklyDivisible]

/-- A singleton is `k`-weakly divisible if `k ≠ 0`. -/
@[category API, AMS 11]
lemma weaklyDivisible_singleton {k : ℕ} (hk : k ≠ 0) (l : ℕ) : WeaklyDivisible k {l} := by
  simp [WeaklyDivisible, hk]

/-- No non-empty set is `1`-weakly divisible. -/
@[category API, AMS 11]
lemma not_weaklyDivisible_zero {A : _} (h : A.Nonempty) : ¬WeaklyDivisible 0 A := by
  simpa [WeaklyDivisible] using ⟨{_}, by simpa using h.choose_spec⟩

@[category API, AMS 11]
lemma empty_iff_weaklyDivisible_zero {A : _} : WeaklyDivisible 0 A ↔ A = ∅ :=
  ⟨fun h ↦ Finset.not_nonempty_iff_eq_empty.1 <| mt not_weaklyDivisible_zero (not_not.2 h),
    fun h ↦ h ▸ weaklyDivisible_empty _⟩

@[category test, AMS 11]
theorem maxWeaklyDivisible_zero : ∀ k : ℕ, MaxWeaklyDivisible 0 k = 0 := by
  intro k
  simp [MaxWeaklyDivisible, Nat.sSup_def]

@[category test, AMS 11]
theorem maxWeaklyDivisible_one {k : ℕ} (hk : k ≠ 0) : MaxWeaklyDivisible 1 k = 1 := by
  have : {x | ∃ A, WeaklyDivisible k A ∧ (A = ∅ ∨ A = {1}) ∧ #A = x} = {0, 1} := by
    refine Set.ext fun _ => ⟨fun _ => by aesop, ?_⟩
    rintro ⟨_, _⟩
    · simpa using weaklyDivisible_empty k
    · exact ⟨{1}, by simp_all [weaklyDivisible_singleton hk 1]⟩
  simp_all [MaxWeaklyDivisible]

@[category test, AMS 11]
theorem maxWeaklyDivisible_zero_k (N : ℕ) : MaxWeaklyDivisible N 0 = 0 := by
  simp [empty_iff_weaklyDivisible_zero, MaxWeaklyDivisible]

@[category test, AMS 11]
theorem firstPrimesMultiples_one_card_zero (k : ℕ) : (FirstPrimesMultiples 1 k).card = 0 := by
  simp [FirstPrimesMultiples, Finset.filter_singleton]
  intro n h
  by_contra hprime
  have : Nat.Prime 1 := by
    convert Nat.prime_nth_prime n
    exact hprime.symm
  tauto

@[category test, AMS 11]
theorem firstPrimesMultiples_zero_k_card_zero (N : ℕ) : (FirstPrimesMultiples N 0).card = 0 := by
  simp [FirstPrimesMultiples]

/--
An example of a `k`-weakly divisible set is the subset of `{1, ..., N}`
containing the multiples of the first `k` primes.
-/
@[category API, AMS 11]
lemma weaklyDivisible_firstPrimesMultiples (N k : ℕ) :
    WeaklyDivisible k (FirstPrimesMultiples N k) := by
  unfold WeaklyDivisible
  intro s hs
  rw [Finset.mem_powersetCard] at hs
  -- Define the map from s to Fin k
  set f : s → Fin k := fun ⟨x, hx⟩ =>
    have h_exists := (Finset.mem_filter.mp (hs.1 hx)).2
    ⟨Classical.choose h_exists, (Classical.choose_spec h_exists).1⟩
  have hcard_s : Fintype.card s = k + 1 := by simp [hs.2]
  have hcard_fink : Fintype.card (Fin k) = k := Fintype.card_fin k
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by omega)
  intro h_pair
  have hne_val : x.1 ≠ y.1 := by
    intro h_eq
    exact hne (Subtype.ext h_eq)
  have h_coprime := h_pair x.2 y.2 hne_val
  set p := (f x).val.nth Nat.Prime
  have hp_prime : p.Prime := Nat.prime_nth_prime _
  have hp_div_x : p ∣ x.1 := by
    have h_exists := (Finset.mem_filter.mp (hs.1 x.2)).2
    exact (Classical.choose_spec h_exists).2
  have hp_div_y : p ∣ y.1 := by
    have h_exists := (Finset.mem_filter.mp (hs.1 y.2)).2
    have h_eq_f : (f x).val = (f y).val := by rw [heq]
    -- (f y).val is Classical.choose h_exists by definition
    have : p = (Classical.choose h_exists).nth Nat.Prime := by
      dsimp [p]
      rw [h_eq_f]
    rw [this]
    exact (Classical.choose_spec h_exists).2
  have hp_div_gcd : p ∣ x.1.gcd y.1 := Nat.dvd_gcd hp_div_x hp_div_y
  have h_gcd_eq_one : x.1.gcd y.1 = 1 := h_coprime
  rw [h_gcd_eq_one] at hp_div_gcd
  have hp_le_one : p ≤ 1 := Nat.le_of_dvd (by norm_num) hp_div_gcd
  have : p > 1 := hp_prime.one_lt
  omega

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ᵉ (k > 0) (N ≥ (k-1).nth Nat.Prime),
        (MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card)

end Problem
