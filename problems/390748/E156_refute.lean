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

- problem_id: E156_refute
- collection: erdos
- question_id: erdos:156
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/156.lean#erdos_156
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist a maximal Sidon set $A\subset \{1,\ldots,N\}$ of size $O(N^{1/3})$? A question of Erdős, Sárközy, and Sós [ESS94].
- notes: Erdos Problem 156 -- https://www.erdosproblems.com/156
- track: open
- answer_shape: refute
- pair_id: E156
- pair_role: refute
- source_stem: 156
- mathdb_ref: erdos:156
- source_namespace: Erdos156
- source_theorem: erdos_156
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: greedySidonSet_isSidon
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset Filter

namespace Problem

/--
The size of the smallest maximal Sidon set in $\{1, \dots, N\}$.
-/
noncomputable def minMaximalSidonSet (N : ℕ) : ℕ :=
  open scoped Classical in
  sInf (((Icc 1 N).powerset.filter fun (A : Finset ℕ) ↦
    Set.IsMaximalSidonSetIn (A : Set ℕ) N).image card : Set ℕ)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 5]
theorem greedySidonSet_isSidon (n : ℕ) : IsSidon (Finset.greedySidonBelow n : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ eq
  have subset : Finset.greedySidonBelow n ⊆ (Finset.greedySidon.aux n).1 := Finset.filter_subset _ _
  exact (Finset.greedySidon.aux n).1.2 i₁ (subset hi₁) j₁ (subset hj₁) i₂ (subset hi₂) j₂ (subset hj₂) eq

abbrev Target : Prop :=
    ¬ (
      (fun N ↦ (minMaximalSidonSet N : ℝ)) =O[atTop] (fun N ↦ (N : ℝ) ^ (1 / 3 : ℝ))
    )

end Problem
