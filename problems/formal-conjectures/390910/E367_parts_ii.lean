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

- problem_id: E367_parts_ii
- collection: erdos
- question_id: erdos:367
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/367.lean#erdos_367.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Or perhaps even $\prod_{n \leq m < n+k} B_2(m) \ll_k n^2$? van Doorn notes in the comments that this fails for all $k \geq 3$.
- notes: Erdos Problem 367 -- https://www.erdosproblems.com/367
- track: solved
- answer_shape: decide
- source_stem: 367
- mathdb_ref: erdos:367
- source_namespace: Erdos367
- source_theorem: erdos_367.parts.ii
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Asymptotics Filter

namespace Problem

/--
`B r n` is the $r$-full part of $n$: the product of prime powers $p^a \| n$ with $a \geq r$.
-/
def B (r n : ℕ) : ℕ :=
  ∏ i ∈ n.factorization.support with r ≤ n.factorization i, i ^ n.factorization i

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ k : ℕ, 1 ≤ k →
        (fun n ↦ ((∏ m ∈ .Ico n (n + k), B 2 m : ℕ) : ℝ)) =O[atTop]
          fun n ↦ (n : ℝ) ^ (2 : ℝ)

end Problem
