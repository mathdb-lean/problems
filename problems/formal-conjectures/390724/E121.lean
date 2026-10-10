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

- problem_id: E121
- collection: erdos
- question_id: erdos:121
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/121.lean#erdos_121
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $F_{k}(N)$ be the size of the largest $A\subseteq \{1,\ldots,N\}$ such that the product of no $k$ many distinct elements of $A$ is a square. Is $F_5(N)=(1-o(1))N$? Conjectured by Erdős, Sós, and Sárközy [ESS95], who proved $F_2(N)=\left(\frac{6}{\pi^2}+o(1)\right)N$, $F_3(N) = (1-o(1))N$, and also established asymptotics for $F_k(N)$ for all even $k\geq 4$ (in particular $F_k(N)\asymp N/\log N$ for all even $k\geq 4$). Erdős [Er38] earlier proved that $F_4(N)=o(N)$ - indeed, if $\lvert A\rvert \gg N$ and $A\subseteq \{1,\ldots,N\}$ then there is a non-trivial solution to $ab=cd$ with $a,b,c,d\in A$. This problem was answered in the negative by Tao [Ta24], who proved that for any $k\geq 4$ there is some constant $c_k>0$ such that $F_k(N) \leq (1-c_k+o(1))N$. See also [888](https://www.erdosproblems.com/888).
- notes: Erdos Problem 121 -- https://www.erdosproblems.com/121
- track: solved
- answer_shape: decide
- source_stem: 121
- mathdb_ref: erdos:121
- source_namespace: Erdos121
- source_theorem: erdos_121
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Asymptotics

namespace Problem

/-- $F_k(N)$ is the size of the largest $A\subseteq \{1,\ldots,N\}$ such that the product of no
$k$ many distinct elements of $A$ is a square. -/
noncomputable def F (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = k → ¬ IsSquare (∏ n ∈ S, n)) ∧ A.card = m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ (fun N : ℕ => (F 5 N : ℝ)) ~[atTop] fun N : ℕ => (N : ℝ)

end Problem
