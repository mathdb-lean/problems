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

- problem_id: E219
- collection: erdos
- question_id: erdos:219
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/219.lean#erdos_219
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there arbitrarily long arithmetic progressions of primes? Solution: yes. Ref: Green, Ben and Tao, Terence, _The primes contain arbitrarily long arithmetic progressions_
- notes: Erdos Problem 219 -- https://www.erdosproblems.com/219
- track: solved
- answer_shape: decide
- source_stem: 219
- mathdb_ref: erdos:219
- source_namespace: Erdos219
- source_theorem: erdos_219
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: primeArithmeticProgression_3_5_7 not_primeArithmeticProgression_1_2 empty_not_primeArithmeticProgression singleton_mem_primeArithmeticProgressions pair_mem_primeArithmeticProgressions
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/--
The set of arithmetic progressions of primes
-/
def primeArithmeticProgressions : Set (Set ℕ) :=
  {s | (∀ p ∈ s, p.Prime) ∧ ∃ l > 0, s.IsAPOfLength l}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 5 11]
theorem primeArithmeticProgression_3_5_7 : {3, 5, 7} ∈ primeArithmeticProgressions := by
  simp only [primeArithmeticProgressions, gt_iff_lt, Set.IsAPOfLength, Set.IsAPOfLengthWith,
    smul_eq_mul, exists_prop, exists_and_left, existsAndEq, true_and, Set.mem_ofPred_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    ENat.card_eq_coe_fintype_card, Fintype.card_ofFinset, Set.toFinset_insert,
    Set.toFinset_singleton, Finset.mem_insert, Nat.reduceEqDiff, Finset.mem_singleton, or_self,
    not_false_eq_true, Finset.card_insert_of_notMem, Finset.card_singleton, Nat.reduceAdd,
    Nat.cast_ofNat, Nat.ofNat_pos, Nat.cast_lt_ofNat]
  refine ⟨by norm_num, ⟨3, 2, Set.ext fun x => ?_⟩⟩
  refine ⟨?_, fun ⟨w, ⟨hl, hr⟩⟩ => by interval_cases w <;> simp_all⟩
  rintro (rfl | rfl | rfl)
  · simp
  · simpa using ⟨1, by simp⟩
  · simpa using ⟨2, by simp⟩

@[category test, AMS 5 11]
theorem not_primeArithmeticProgression_1_2 : ¬{1, 2} ∈ primeArithmeticProgressions := by
  simp [primeArithmeticProgressions]

@[category API, AMS 5 11]
theorem empty_not_primeArithmeticProgression : ∅ ∉ primeArithmeticProgressions := by
  simpa [primeArithmeticProgressions] using fun _ hl ↦ Set.not_isAPOfLength_empty hl

@[category API, AMS 5 11]
lemma singleton_mem_primeArithmeticProgressions
    {p : ℕ} (hp : p.Prime) : {p} ∈ primeArithmeticProgressions := by
  simpa [primeArithmeticProgressions, hp] using ⟨1, one_pos, by simp⟩

@[category API, AMS 5 11]
lemma pair_mem_primeArithmeticProgressions
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    {p, q} ∈ primeArithmeticProgressions := by
  let ⟨n, h⟩ := Nat.exists_eq_add_of_lt hpq
  simpa [primeArithmeticProgressions, hp, hq] using ⟨2, by norm_num, Nat.isAPOfLength_pair hpq⟩

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ N : ℕ, ∃ l ∈ primeArithmeticProgressions, N ≤ ENat.card l

end Problem
