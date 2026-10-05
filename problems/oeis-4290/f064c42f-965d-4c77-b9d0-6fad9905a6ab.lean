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

- problem_id: O4290_conjecture
- collection: oeis
- question_id: oeis:4290
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/4290.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: It is known that $a(10^k - 1) = (10^{9k} - 1) / 9$ for all $k$. Is $a(n) < a(10^k - 1)$ for all $n < 10^k - 1$? - David Radcliffe, Aug 01 2025
- notes: OEIS A4290 -- https://oeis.org/A4290
- track: open
- answer_shape: proof
- source_stem: 4290
- source_namespace: OeisA4290
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_ten_pow
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Least positive multiple of $n$ using only 0's and 1's in base 10. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  dsimp [a]
  have h_empty : { m : ℕ | 0 < m ∧ 0 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } = ∅ := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hm h0dvd
    have hm0 : m = 0 := Nat.eq_zero_of_zero_dvd h0dvd
    omega
  rw [h_empty, Nat.sInf_empty]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  have h_least : IsLeast { m : ℕ | 0 < m ∧ 1 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } 1 := by
    refine ⟨⟨by decide, dvd_rfl, ?_⟩, fun m hm ↦ hm.1⟩
    intro d hd
    rw [Nat.digits_def' (by decide) (by decide), show (1 / 10 : ℕ) = 0 by rfl,
      Nat.digits_zero] at hd
    simp only [show 1 % 10 = 1 by rfl, List.mem_singleton] at hd
    subst hd
    exact Or.inr rfl
  exact h_least.csInf_eq

@[category test, AMS 11]
theorem a_2 : a 2 = 10 := by
  dsimp [a]
  have h_least : IsLeast { m : ℕ | 0 < m ∧ 2 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } 10 := by
    refine ⟨⟨by decide, by decide, ?_⟩, ?_⟩
    · intro d hd
      have h10 : (10 : ℕ) = 10 ^ 1 * 1 := by rfl
      nth_rw 2 [h10] at hd
      rw [Nat.digits_base_pow_mul (b := 10) (k := 1) (m := 1) (by decide) (by decide),
          Nat.digits_of_lt 10 1 (by decide) (by decide)] at hd
      simp only [List.replicate_one, List.singleton_append, List.mem_cons,
        List.not_mem_nil, or_false] at hd
      exact hd
    · intro m hm
      by_contra! hlt
      have hm_pos : 0 < m := hm.1
      have h2dvd : 2 ∣ m := hm.2.1
      have hd : ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := hm.2.2
      interval_cases m
      · revert h2dvd; decide
      · have hm_d : Nat.digits 10 2 = [2] := Nat.digits_of_lt 10 2 (by decide) (by decide)
        have h_mem : 2 ∈ Nat.digits 10 2 := by rw [hm_d]; exact List.Mem.head []
        have := hd 2 h_mem; omega
      · have hm_d : Nat.digits 10 3 = [3] := Nat.digits_of_lt 10 3 (by decide) (by decide)
        have h_mem : 3 ∈ Nat.digits 10 3 := by rw [hm_d]; exact List.Mem.head []
        have := hd 3 h_mem; omega
      · have hm_d : Nat.digits 10 4 = [4] := Nat.digits_of_lt 10 4 (by decide) (by decide)
        have h_mem : 4 ∈ Nat.digits 10 4 := by rw [hm_d]; exact List.Mem.head []
        have := hd 4 h_mem; omega
      · have hm_d : Nat.digits 10 5 = [5] := Nat.digits_of_lt 10 5 (by decide) (by decide)
        have h_mem : 5 ∈ Nat.digits 10 5 := by rw [hm_d]; exact List.Mem.head []
        have := hd 5 h_mem; omega
      · have hm_d : Nat.digits 10 6 = [6] := Nat.digits_of_lt 10 6 (by decide) (by decide)
        have h_mem : 6 ∈ Nat.digits 10 6 := by rw [hm_d]; exact List.Mem.head []
        have := hd 6 h_mem; omega
      · have hm_d : Nat.digits 10 7 = [7] := Nat.digits_of_lt 10 7 (by decide) (by decide)
        have h_mem : 7 ∈ Nat.digits 10 7 := by rw [hm_d]; exact List.Mem.head []
        have := hd 7 h_mem; omega
      · have hm_d : Nat.digits 10 8 = [8] := Nat.digits_of_lt 10 8 (by decide) (by decide)
        have h_mem : 8 ∈ Nat.digits 10 8 := by rw [hm_d]; exact List.Mem.head []
        have := hd 8 h_mem; omega
      · have hm_d : Nat.digits 10 9 = [9] := Nat.digits_of_lt 10 9 (by decide) (by decide)
        have h_mem : 9 ∈ Nat.digits 10 9 := by rw [hm_d]; exact List.Mem.head []
        have := hd 9 h_mem; omega
  exact h_least.csInf_eq

/-- $a(10^k) = 10^k$ for all $k$. -/
@[category textbook, AMS 11]
theorem a_ten_pow (k : ℕ) : a (10 ^ k) = 10 ^ k := by
  dsimp [a]
  have h_least : IsLeast { m : ℕ | 0 < m ∧ 10 ^ k ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } (10 ^ k) := by
    refine ⟨⟨Nat.pow_pos (by decide), dvd_rfl, ?_⟩, fun m hm ↦ Nat.le_of_dvd hm.1 hm.2.1⟩
    intro d hd
    have h10k : 10 ^ k = 10 ^ k * 1 := by rw [mul_one]
    rw [h10k, Nat.digits_base_pow_mul (b := 10) (k := k) (m := 1) (by decide) (by decide),
        Nat.digits_of_lt 10 1 (by decide) (by decide)] at hd
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
    rcases hd with ⟨-, rfl⟩ | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact h_least.csInf_eq

abbrev Target : Prop :=
    ∀ (k : ℕ),
      ∀ n < 10 ^ k - 1, a n < a (10 ^ k - 1)

end Problem
