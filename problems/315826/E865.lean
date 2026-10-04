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

- problem_id: E865
- collection: erdos
- question_id: erdos:865
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/865.lean#erdos_865
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There exists a constant $C>0$ such that, for all large $N$, if $A\subseteq \{1,\ldots,N\}$ has size at least $\frac{5}{8}N+C$ then there are distinct $a,b,c\in A$ such that $a+b,a+c,b+c\in A$. A problem of Erdős and Sós (also earlier considered by Choi, Erdős, and Szemerédi [CES75], but Erdős had forgotten this). This problem was solved in the affirmative by Cipollini and GPT Pro [Ci26]. This is true. The linked proof gives it in the contrapositive and with the constant cleared: every triple-free $A\subseteq\{1,\ldots,N\}$ satisfies $8\lvert A\rvert\leq 5N+C$ for a fixed $C$, for every $N$ rather than only for large $N$. It also shows the threshold is sharp, by exhibiting triple-free sets of size $(5N+16)/8$ for every $N$ divisible by $8$.
- notes: Erdos Problem 865 -- https://www.erdosproblems.com/865
- track: solved
- answer_shape: proof
- source_stem: 865
- mathdb_ref: erdos:865
- source_namespace: Erdos865
- source_theorem: erdos_865
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset Filter
open scoped Asymptotics

namespace Problem

noncomputable def f (N k : ℕ) : ℕ :=
  sInf {m | ∀ A ⊆ Icc 1 N, A.card ≥ m →
    ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A}

abbrev Target : Prop :=
    ∃ C > 0, ∀ᶠ (N : ℕ) in atTop,
      ∀ A ⊆ Icc 1 N, A.card ≥ (5 / 8 : ℝ) * N + C →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

end Problem
