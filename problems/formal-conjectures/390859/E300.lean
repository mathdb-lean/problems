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

- problem_id: E300
- collection: erdos
- question_id: erdos:300
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/300.lean#erdos_300
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A(N)$ denote the maximal cardinality of $A\subseteq \{1,\ldots,N\}$ such that $\sum_{n\in S}\frac{1}{n}\neq 1$ for all $S\subseteq A$. Estimate $A(N)$. Erdős and Graham [ErGr80] believe the answer is $A(N)=(1+o(1))N$. Croot [Cr03] disproved this, showing the existence of some constant $c<1$ such that $A(N)<cN$ for all large $N$. It is trivial that $A(N)\geq (1-\frac{1}{e}+o(1))N$. Liu and Sawhney [LiSa24] have proved that $A(N)=(1-1/e+o(1))N$.
- notes: Erdos Problem 300 -- https://www.erdosproblems.com/300
- track: solved
- answer_shape: proof
- source_stem: 300
- mathdb_ref: erdos:300
- source_namespace: Erdos300
- source_theorem: erdos_300
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Topology

namespace Problem

/-- $A(N)$ is the maximal cardinality of $A\subseteq \{1,\ldots,N\}$ such that
$\sum_{n\in S}\frac{1}{n}\neq 1$ for all $S\subseteq A$. -/
noncomputable def A (N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 N ∧ (∀ S ⊆ B, ∑ n ∈ S, (1 / n : ℚ) ≠ 1) ∧
    B.card = m}

abbrev Target : Prop :=
    Tendsto (fun N : ℕ => (A N : ℝ) / N) atTop (𝓝 (1 - 1 / Real.exp 1))

end Problem
