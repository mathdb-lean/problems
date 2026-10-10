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

- problem_id: E292
- collection: erdos
- question_id: erdos:292
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/292.lean#erdos_292
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be the set of $n\in \mathbb{N}$ such that there exist $1\leq m_1<\cdots <m_k=n$ with $\sum\tfrac{1}{m_i}=1$. Explore $A$. In particular, does $A$ have density $1$? Straus observed that $A$ is closed under multiplication. Furthermore, it is easy to see that $A$ does not contain any prime power. The answer is yes, as proved by Martin [Ma00], who in fact proved that if $B=\mathbb{N}\backslash A$ then, for all large $x$, $$\frac{\lvert B\cap [1,x]\rvert}{x}\asymp \frac{\log\log x}{\log x},$$ and also gave an essentially complete description of $B$ as those integers which are small multiples of prime powers. van Doorn has observed that if $n\in A$ (with $n>1$) then $2n\in A$ also, since if $\sum \frac{1}{m_i}=1$ then $\frac{1}{2}+\sum\frac{1}{2m_i}=1$ also.
- notes: Erdos Problem 292 -- https://www.erdosproblems.com/292
- track: solved
- answer_shape: decide
- source_stem: 292
- mathdb_ref: erdos:292
- source_namespace: Erdos292
- source_theorem: erdos_292
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Asymptotics

namespace Problem

/-- The set $A$ of $n\in \mathbb{N}$ such that there exist $1\leq m_1<\cdots <m_k=n$ with
$\sum\tfrac{1}{m_i}=1$. -/
def A : Set ℕ :=
  {n | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ ∑ m ∈ S, (1 : ℚ) / m = 1}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ A.HasDensity 1

end Problem
