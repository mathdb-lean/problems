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

- problem_id: O119591_conjecture
- collection: oeis
- question_id: oeis:119591
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/119591.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is $a(n)$ defined for all $n \ge 2$? That is, does there exist $k > 0$ such that $2 \cdot n^k - 1$ is prime?
- notes: OEIS A119591 -- https://oeis.org/A119591
- track: open
- answer_shape: proof
- source_stem: 119591
- source_namespace: OeisA119591
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_5 a_6
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Least $k \ge 1$ such that $2 \cdot n^k - 1$ is prime, or $0$ if no such $k$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ (2 * n ^ k - 1).Prime}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  dsimp [a]
  have h_empty : {k : ℕ | 0 < k ∧ (2 * 0 ^ k - 1).Prime} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hk
    rw [zero_pow hk.ne', mul_zero, show (0 - 1 : ℕ) = 0 from rfl]
    exact Nat.not_prime_zero
  rw [h_empty, Nat.sInf_empty]

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  dsimp [a]
  have h_empty : {k : ℕ | 0 < k ∧ (2 * 1 ^ k - 1).Prime} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _
    rw [one_pow, mul_one, show (2 - 1 : ℕ) = 1 from rfl]
    exact Nat.not_prime_one
  rw [h_empty, Nat.sInf_empty]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 2 ^ k - 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 3 ^ k - 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 4 ^ k - 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 5 ^ k - 1).Prime} 4 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra! h
      have hk_pos := hk.1
      interval_cases k
      · have hk2 := hk.2
        revert hk2
        norm_num
      · have hk2 := hk.2
        revert hk2
        norm_num
      · have hk2 := hk.2
        revert hk2
        norm_num
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 6. -/
@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 6 ^ k - 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 2 ≤ n),
      ∃ k > 0, (2 * n ^ k - 1).Prime

end Problem
