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

- problem_id: E15_prove
- collection: erdos
- question_id: erdos:15
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/15.lean#erdos_15
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that $\sum_{n=1}^\infty(-1)^n\frac{n}{p_n}$ converges, where $p_n$ is the sequence of primes? Note: In the problem statement, $p_n$ is the $n$-th prime, indexed such that $p_1=2, p_2=3, \ldots$. We 0-index here to reflect how Nat.nth works. Note: convergence here is convergence of the sequence of partial sums, which is what the problem asks about. `Summable` would be the wrong notion: it is unconditional summability, equivalent over $\mathbb{R}$ to absolute convergence, and $\sum_n n/p_n$ diverges.
- notes: Erdos Problem 15 -- https://www.erdosproblems.com/15
- track: open
- answer_shape: prove
- pair_id: E15
- pair_role: prove
- source_stem: 15
- mathdb_ref: erdos:15
- source_namespace: Erdos15
- source_theorem: erdos_15
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter Topology

abbrev Target : Prop :=
    ∃ l : ℝ, Tendsto (fun N => ∑ k ∈ Finset.range N,
          (-1 : ℝ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime)) atTop (𝓝 l)

end Problem
