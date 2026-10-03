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

- problem_id: E148
- collection: erdos
- question_id: erdos:148
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/148.lean#erdos_148
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $F(k)$ be the number of solutions to $$ 1= \frac{1}{n_1}+\cdots+\frac{1}{n_k},$$ where $1\leq n_1<\cdots<n_k$ are distinct integers. Find good estimates for $F(k)$.
- notes: Erdos Problem 148 -- https://www.erdosproblems.com/148
- track: open
- answer_shape: value
- answer_type: ℕ → ℝ
- answer_pinned: false
- answer_pinned_reason: relation_is_reflexive
- source_stem: 148
- mathdb_ref: erdos:148
- source_namespace: Erdos148
- source_theorem: erdos_148
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: F_one u_first_values
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real

namespace Problem

/-- `F k` is the number of solutions to $1 = \frac{1}{n_1} + \cdots + \frac{1}{n_k}$ with
$1 \leq n_1 < \cdots < n_k$, that is, the number of $k$-element sets of positive integers whose
reciprocals sum to $1$. -/
noncomputable def F (k : ℕ) : ℕ :=
  {S : Finset ℕ | S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℚ) / n = 1}.ncard

/-- The sequence $u_0 = 1$, $u_{n+1} = u_n(u_n + 1)$ of [ElPl21, Corollary 3]:
$1, 2, 6, 42, 1806, \ldots$, a shifted copy of Sylvester's sequence. This is the sequence
`Erdos315.u` of Erdős Problem 315. -/
def u : ℕ → ℕ
  | 0 => 1
  | n + 1 => u n * (u n + 1)

/-- The constant $c_0 = \lim_{n \to \infty} u_n^{2^{-n}} = 1.5979102\ldots$ of
[ElPl21, Corollary 3]. The sequence $u_n^{2^{-n}}$ is increasing and bounded by $2$
[ElPl21, Remark 3], so the limit is its supremum. This constant is the square of the Vardi
constant $1.26408\ldots$, which is `Erdos315.c₀`. -/
noncomputable def c₀ : ℝ := ⨆ n : ℕ, (u n : ℝ) ^ ((1 : ℝ) / 2 ^ n)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The only representation of $1$ as a single unit fraction is $1 = \frac{1}{1}$. -/
@[category test, AMS 11]
theorem F_one : F 1 = 1 := by
  have h : {S : Finset ℕ | S.card = 1 ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℚ) / n = 1} =
      {{1}} := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.card_eq_one]
    constructor
    · rintro ⟨⟨a, rfl⟩, -, hsum⟩
      simp only [Finset.sum_singleton, one_div, inv_eq_one, Nat.cast_eq_one] at hsum
      rw [hsum]
    · rintro rfl
      exact ⟨⟨1, rfl⟩, by simp, by simp⟩
  rw [F, h, Set.ncard_singleton]

/-- The first values of the sequence are $1, 2, 6, 42, 1806$. -/
@[category test, AMS 11]
theorem u_first_values : u 0 = 1 ∧ u 1 = 2 ∧ u 2 = 6 ∧ u 3 = 42 ∧ u 4 = 1806 := by
  decide

abbrev Target (value : ℕ → ℝ) : Prop :=
    (fun k ↦ (F k : ℝ)) =Θ[atTop] value

end Problem
