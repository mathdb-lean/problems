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

- problem_id: E858
- collection: erdos
- question_id: erdos:858
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/858.lean#erdos_858
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \{1,\ldots,N\}$ be such that there is no solution to $at=b$ with $a,b\in A$ and the smallest prime factor of $t$ is $>a$. Estimate the maximum of $$\frac{1}{\log N}\sum_{n\in A}\frac{1}{n}.$$ This has been solved by Chojecki and GPT-5.4 Pro, who show that for large $N$ $$\max_A \sum_{n\in A}\frac{1}{n}=(c+o(1))\log N$$ where the maximum is over all $A\subseteq \{1,\ldots,N\}$ with the stated property and $c\approx 0.618\cdots$ is an explicit constant.
- notes: Erdos Problem 858 -- https://www.erdosproblems.com/858
- track: solved
- answer_shape: proof
- source_stem: 858
- mathdb_ref: erdos:858
- source_namespace: Erdos858
- source_theorem: erdos_858
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real

namespace Problem

/-- `A` has no solution to $at=b$ with $a,b\in A$ and the smallest prime factor of $t$
greater than $a$. -/
def IsAdmissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, a * t = b → t.minFac ≤ a

/-- The maximum of $\sum_{n\in A}\frac{1}{n}$ over all admissible $A\subseteq \{1,\ldots,N\}$. -/
noncomputable def M (N : ℕ) : ℝ :=
  sSup {m | ∃ A ⊆ Finset.Icc 1 N, IsAdmissible A ∧ ∑ n ∈ A, (1 : ℝ) / n = m}

abbrev Target : Prop :=
    ∃ c : ℝ, Tendsto (fun N : ℕ ↦ M N / log N) atTop (nhds c)

end Problem
