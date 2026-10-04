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

- problem_id: E42
- collection: erdos
- question_id: erdos:42
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/42.lean#erdos_42
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 42**: Let M ≥ 1 and N be sufficiently large in terms of M. Is it true that for every maximal Sidon set `A ⊆ {1,…,N}` there is another Sidon set `B ⊆ {1,…,N}` of size M such that `(A - A) ∩ (B - B) = {0}`? This was proved for all $M$ by GPT 5.5 Pro (prompted by Sandhu), see discussion thread for more details.
- notes: Erdos Problem 42 -- https://www.erdosproblems.com/42
- track: solved
- answer_shape: decide
- source_stem: 42
- mathdb_ref: erdos:42
- source_namespace: Erdos42
- source_theorem: erdos_42
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: example_maximal_sidon example_difference_set maximal_sidon_contains_zero
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Function Set Filter
open scoped Pointwise

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-  ## Related results and examples -/

/--
The set `{1, 2, 4}` is a maximal Sidon set in `{1, ..., 4}`.
-/
@[category textbook, AMS 5 11]
theorem example_maximal_sidon : IsMaximalSidonSetIn {1, 2, 4} 4 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp [Set.mem_Icc]
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
    rcases hi₁ with rfl | rfl | rfl <;>
    rcases hj₁ with rfl | rfl | rfl <;>
    rcases hi₂ with rfl | rfl | rfl <;>
    rcases hj₂ with rfl | rfl | rfl <;>
    simp_all
  · intro x hx hxA
    simp only [Set.mem_Icc] at hx; obtain ⟨hx1, hx2⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxA
    obtain ⟨hne1, hne2, hne4⟩ := hxA
    have hx3 : x = 3 := (by omega); subst hx3
    intro hbad
    have := hbad 1 (by simp) 2 (by simp) 3 (by simp) 2 (by simp) (by norm_num)
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/--
The difference set of `{1, 2, 4}` is `{0, 1, 2, 3}`.
-/
@[category textbook, AMS 5 11]
theorem example_difference_set : ({1, 2, 4} : Set ℕ) - {1, 2, 4} = {0, 1, 2, 3} := by
  ext x
  simp only [Set.mem_sub, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, by decide, 1, by decide, by decide⟩
    · exact ⟨2, by decide, 1, by decide, by decide⟩
    · exact ⟨4, by decide, 2, by decide, by decide⟩
    · exact ⟨4, by decide, 1, by decide, by decide⟩

/--
For any maximal Sidon set, the difference set contains 0.
-/
@[category textbook, AMS 5 11]
theorem maximal_sidon_contains_zero (A : Set ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hA : IsMaximalSidonSetIn A N) : 0 ∈ A - A := by
  obtain ⟨hAsub, hAsidon, hAmax⟩ := hA
  have hne : A.Nonempty
  · by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
    exact hAmax (Set.mem_Icc.mpr ⟨le_refl 1, hN⟩)
      (by rw [hemp]; exact id) (by
        rw [hemp, Set.empty_union]
        exact fun _ hi _ hj _ hk _ hl _ => by
          simp only [Set.mem_singleton_iff] at hi hj hk hl
          subst hi
          subst hj
          subst hk
          subst hl
          exact Or.inl ⟨rfl, rfl⟩)
  obtain ⟨a, ha⟩ := hne
  have := Set.sub_mem_sub ha ha
  rwa [Nat.sub_self] at this

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
        ∃ᵉ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B)) = {0}

end Problem
