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

- problem_id: E877
- collection: erdos
- question_id: erdos:877
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/877.lean#erdos_877
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f_m(n)$ count the number of maximal sum-free subsets $A\subseteq\{1,\ldots,n\}$ - that is, there are no solutions to $a=b+c$ in $A$ and $A$ is maximal with this property. Estimate $f(n)$ - is it true that $f_m(n)=o(2^{n/2})$? A problem of Cameron and Erdős. Łuczak and Schoen [LuSc01] proved that there exists a constant $c<1/2$ such that $f_m(n)<2^{cn}$, resolving this question. Balogh, Liu, Sharifzadeh, and Treglown [BLST15] proved that $f_m(n)=2^{(\frac{1}{4}+o(1))n}$. See [748](https://www.erdosproblems.com/748) for the non-maximal case.
- notes: Erdos Problem 877 -- https://www.erdosproblems.com/877
- track: solved
- answer_shape: decide
- source_stem: 877
- mathdb_ref: erdos:877
- source_namespace: Erdos877
- source_theorem: erdos_877
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Asymptotics Real

namespace Problem

/-- `A` is a maximal sum-free subset of `{1, …, n}`. -/
def IsMaximalSumFree (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ IsSumFree (A : Set ℕ) ∧
    ∀ B ⊆ Finset.Icc 1 n, IsSumFree (B : Set ℕ) → A ⊆ B → A = B

open scoped Classical in
/-- `fm n` counts the number of maximal sum-free subsets $A\subseteq\{1,\ldots,n\}$. -/
noncomputable def fm (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsMaximalSumFree n A).card

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        (fun n : ℕ ↦ (fm n : ℝ)) =o[atTop] fun n : ℕ ↦ (2 : ℝ) ^ ((n : ℝ) / 2)

end Problem
