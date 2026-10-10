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

- problem_id: E973
- collection: erdos
- question_id: erdos:973
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/973.lean#erdos_973
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist a constant $C>1$ such that, for every $n\geq 2$, there exists a sequence $z_i\in \mathbb{C}$ with $z_1=1$ and $\lvert z_i\rvert \geq 1$ for all $1\leq i\leq n$ with $\max_{2\leq k\leq n+1}\left\lvert \sum_{1\leq i\leq n}z_i^k\right\rvert < C^{-n}$? This is Problem 7.3 in [Ha74], where it is attributed to Erdős. The answer is no, by Luo, Yang and Zhu [LYZ26]: the maximum exceeds $e^{-\lambda n}$ for every fixed $\lambda>0$ once $n$ is large, so it decays subexponentially and no such $C$ exists. See `erdos_973.variants.luo_yang_zhu` below.
- notes: Erdos Problem 973 -- https://www.erdosproblems.com/973
- track: solved
- answer_shape: decide
- source_stem: 973
- mathdb_ref: erdos:973
- source_namespace: Erdos973
- source_theorem: erdos_973
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Finset Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∃ C : ℝ, C > 1 ∧
        ∀ n : ℕ, n ≥ 2 → ∃ z : ℕ → ℂ,
          z 1 = 1 ∧
          (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) ∧
          (∀ k ∈ Icc 2 (n + 1), ‖∑ i ∈ Icc 1 n, z i ^ k‖ < C ^ (-(n : ℝ)))

end Problem
