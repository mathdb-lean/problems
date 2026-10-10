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

- problem_id: E748
- collection: erdos
- question_id: erdos:748
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/748.lean#erdos_748
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)$ count the number of sum-free $A\subseteq \{1,\ldots,n\}$, i.e. $A$ contains no solutions to $a=b+c$ with $a,b,c\in A$. Is it true that $$f(n)=2^{(1+o(1))\frac{n}{2}}?$$ The Cameron–Erdős conjecture. This is true, and in fact $f(n) \ll 2^{n/2}$, which was proved independently by Green [Gr04] and Sapozhenko [Sa03]. The statement $f(n)=2^{(1+o(1))n/2}$ is formalised as $\log_2 f(n)/n\to 1/2$.
- notes: Erdos Problem 748 -- https://www.erdosproblems.com/748
- track: solved
- answer_shape: decide
- source_stem: 748
- mathdb_ref: erdos:748
- source_namespace: Erdos748
- source_theorem: erdos_748
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Real

namespace Problem

open scoped Classical in
/-- `f n` counts the number of sum-free $A\subseteq \{1,\ldots,n\}$, i.e. $A$ contains no
solutions to $a=b+c$ with $a,b,c\in A$. -/
noncomputable def f (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ)).card

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        Tendsto (fun n : ℕ ↦ logb 2 (f n) / n) atTop (nhds (1 / 2))

end Problem
