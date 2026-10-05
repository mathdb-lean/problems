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

- problem_id: E867
- collection: erdos
- question_id: erdos:867
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/867.lean#erdos_867
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that if $A=\{a_1<\cdots <a_t\}\subseteq \{1,\ldots,N\}$ has no solutions to $$a_i+a_{i+1}+\cdots+a_j\in A$$ then $$\lvert A\rvert \leq \frac{N}{2}+O(1)?$$ In fact this problem is false. Freud [Fr93] constructed a sequence with density $\geq 19/36$. The current best bounds are due to Coppersmith and Phillips [CoPh96], who prove that the maximal size of such an $A$ satisfies $$\frac{13}{24}N -O(1)\leq \lvert A\rvert \leq \left(\frac{2}{3}-\frac{1}{512}\right)N+\log N.$$
- notes: Erdos Problem 867 -- https://www.erdosproblems.com/867
- track: solved
- answer_shape: decide
- source_stem: 867
- mathdb_ref: erdos:867
- source_namespace: Erdos867
- source_theorem: erdos_867
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

/-- A finite set of naturals $A=\{a_1<\cdots<a_t\}$ is *consecutive-sum-free* if it has no
solutions to $a_i+a_{i+1}+\cdots+a_j\in A$ with $i<j$; equivalently, whenever an interval
$[m,n]$ contains at least two elements of $A$, the sum of the elements of $A$ lying in
$[m,n]$ is not itself an element of $A$. -/
def ConsecutiveSumFree (A : Finset ℕ) : Prop :=
  ∀ m n : ℕ, 2 ≤ (Finset.Icc m n ∩ A).card → (∑ a ∈ Finset.Icc m n ∩ A, a) ∉ A

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ C : ℝ, ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N, ConsecutiveSumFree A →
          (A.card : ℝ) ≤ (N : ℝ) / 2 + C

end Problem
