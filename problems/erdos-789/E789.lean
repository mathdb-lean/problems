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

- problem_id: E789
- collection: erdos
- question_id: erdos:789
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/789.lean#erdos_789
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $h(n)$ be maximal such that if $A\subseteq \mathbb{Z}$ with $\lvert A\rvert=n$ then there is $B\subseteq A$ with $\lvert B\rvert \geq h(n)$ such that if $a_1+\cdots+a_r=b_1+\cdots+b_s$ with $a_i,b_i\in B$ then $r=s$. Estimate $h(n)$.
- notes: Erdos Problem 789 -- https://www.erdosproblems.com/789
- track: open
- answer_shape: value
- answer_type: ℕ → ℝ
- answer_pinned: false
- answer_pinned_reason: relation_is_reflexive
- source_stem: 789
- mathdb_ref: erdos:789
- source_namespace: Erdos789
- source_theorem: erdos_789
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

open scoped Asymptotics Finset

namespace Problem

/-- Given a non-negative integer $n$, we say $m$ is a separating cardinality of
subset sums if, for any set $A$ of $n$ integers, there is some $B\subseteq A$ of
size $\geq m$ such that subset sums of $B$ can only ever coincide when the
subsets have the same cardinality. -/
def IsSubsetSumSeparatingCard (n m : ℕ) : Prop :=
  ∀ A : Finset ℤ, #A = n → ∃ B : Finset ℤ, B ⊆ A ∧ m ≤ #B ∧
    (∀ᵉ (T ⊆ B) (S ⊆ B), S.Nonempty → T.Nonempty → ∑ a ∈ T, a = ∑ b ∈ S, b → #T = #S)

/-- The subset sum threshold $h(n)$, for each positive $n$, is the maximal separating
cardinality of subset sums for $n$. -/
noncomputable def subsetSumThreshold (n : ℕ): ℕ :=
  sSup { m | IsSubsetSumSeparatingCard n m }

abbrev Target (value : ℕ → ℝ) : Prop :=
    (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] value

end Problem
