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

- problem_id: O86766_conjecture2
- collection: oeis
- question_id: oeis:86766
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/86766.lean#conjecture2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: If $n$ is not of the form $10^m$ then $a(n)$ is nonzero. - _Farideh Firoozbakht_, Jan 07 2015
- notes: OEIS A86766 -- https://oeis.org/A86766
- track: open
- answer_shape: proof
- source_stem: 86766
- source_namespace: OeisA86766
- source_theorem: conjecture2
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Sequence $a(n)$ is the smallest $r > 0$ such that the concatenation of $n$, $r$ times
with itself, multiplied by $10$ plus $1$, is prime, or $0$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let ℓ : ℕ := (Nat.digits 10 n).length
    let M : ℕ := 10 ^ ℓ
    let repCatVal (r : ℕ) : ℕ := n * ∑ i ∈ Finset.range r, M ^ i
    let primeCandidate (r : ℕ) : ℕ := repCatVal r * 10 + 1
    sInf {r : ℕ | 0 < r ∧ (primeCandidate r).Prime}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  have h_least : IsLeast {r : ℕ | 0 < r ∧ ((1 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  1).length) ^ i) * 10 + 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by omega, ?_⟩
      have : (Nat.digits 10 1).length = 1 := by decide
      rw [this]
      norm_num
    · intro r hr
      simp only [Set.mem_ofPred_eq] at hr
      exact hr.1
  have ha1 : a 1 = sInf {r : ℕ | 0 < r ∧ ((1 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  1).length) ^ i) * 10 + 1).Prime} := by
    unfold a
    split <;> [omega; rfl]
  rw [ha1, h_least.csInf_eq]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  have h_digits : (Nat.digits 10 2).length = 1 := by decide
  have h_least : IsLeast {r : ℕ | 0 < r ∧ ((2 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  2).length) ^ i) * 10 + 1).Prime} 3 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by omega, ?_⟩
      rw [h_digits]
      norm_num
    · intro r hr
      simp only [Set.mem_ofPred_eq] at hr
      by_contra! h
      have hr_pos := hr.1
      interval_cases r
      · have hr2 := hr.2
        rw [h_digits] at hr2
        revert hr2
        norm_num
      · have hr2 := hr.2
        rw [h_digits] at hr2
        revert hr2
        norm_num
  have ha2 : a 2 = sInf {r : ℕ | 0 < r ∧ ((2 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  2).length) ^ i) * 10 + 1).Prime} := by
    unfold a
    split <;> [omega; rfl]
  rw [ha2, h_least.csInf_eq]

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  have h_least : IsLeast {r : ℕ | 0 < r ∧ ((3 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  3).length) ^ i) * 10 + 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by omega, ?_⟩
      have : (Nat.digits 10 3).length = 1 := by decide
      rw [this]
      norm_num
    · intro r hr
      simp only [Set.mem_ofPred_eq] at hr
      exact hr.1
  have ha3 : a 3 = sInf {r : ℕ | 0 < r ∧ ((3 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  3).length) ^ i) * 10 + 1).Prime} := by
    unfold a
    split <;> [omega; rfl]
  rw [ha3, h_least.csInf_eq]

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  have h_least : IsLeast {r : ℕ | 0 < r ∧ ((4 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  4).length) ^ i) * 10 + 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by omega, ?_⟩
      have : (Nat.digits 10 4).length = 1 := by decide
      rw [this]
      norm_num
    · intro r hr
      simp only [Set.mem_ofPred_eq] at hr
      exact hr.1
  have ha4 : a 4 = sInf {r : ℕ | 0 < r ∧ ((4 * ∑ i ∈ Finset.range r, (10 ^ (Nat.digits 10
  4).length) ^ i) * 10 + 1).Prime} := by
    unfold a
    split <;> [omega; rfl]
  rw [ha4, h_least.csInf_eq]

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 0 < n) (h : ∀ m : ℕ, n ≠ 10 ^ m),
      a n ≠ 0

end Problem
