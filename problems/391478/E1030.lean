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

- problem_id: E1030
- collection: erdos
- question_id: erdos:1030
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1030.lean#erdos_1030
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $R(k,l)$ be the usual Ramsey number: the smallest $n$ such that if the edges of $K_n$ are coloured red and blue then there exists either a red $K_k$ or a blue $K_l$. Prove the existence of some $c>0$ such that $$\lim_{k\to \infty}\frac{R(k+1,k)}{R(k,k)}> 1+c.$$ A problem of Erdős and Sós.
- notes: Erdos Problem 1030 -- https://www.erdosproblems.com/1030
- track: open
- answer_shape: proof
- source_stem: 1030
- mathdb_ref: erdos:1030
- source_namespace: Erdos1030
- source_theorem: erdos_1030
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ∃ c > (0 : ℝ), ∃ L : ℝ,
      Tendsto (fun k : ℕ ↦
        (SimpleGraph.classicalRamsey (k + 1) k : ℝ) /
          (SimpleGraph.classicalRamsey k k : ℝ)) atTop (nhds L) ∧
      L > 1 + c

end Problem
