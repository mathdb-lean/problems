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

- problem_id: E341
- collection: erdos
- question_id: erdos:341
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/341.lean#erdos_341
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A=\{a_1 < \cdots < a_k\}$ be a finite set of integers and extend it to an infinite sequence $\overline{A}=\{a_1 < a_2 < \cdots \}$ by defining $a_{n+1}$ for $n \geq k$ to be the least integer exceeding $a_n$ which is not of the form $a_i + a_j$ with $i,j \leq n$. Is it true that the sequence of differences $a_{m+1}-a_m$ is eventually periodic? This problem is discussed under Problem 7 on Green's open problems list. The answer is no: Li [Li26] (with GPT-5.6 Sol) showed that the greedy extension of the seed set $A = \{1, 2, 3, 5, 7, 13, 22, 27, 28, 32, 36, 40, 47, 48, 52, 63, 71, 77, 81, 89, 97\}$ has a sequence of differences that is not eventually periodic. The linked formal proof exhibits such a sequence `a : ℕ → ℕ` (strictly increasing, with the greedy rule holding from some index on, and with `n ↦ a (n + 1) - a n` not eventually periodic); casting it to `ℤ` gives a counterexample to the statement below.
- notes: Erdos Problem 341 -- https://www.erdosproblems.com/341
- track: solved
- answer_shape: decide
- source_stem: 341
- mathdb_ref: erdos:341
- source_namespace: Erdos341
- source_theorem: erdos_341
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Nat Set Filter
open scoped Topology

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∀ (a : ℕ → ℤ),
        (∀ᶠ n in atTop,
          IsLeast { x | a n < x ∧ x ∉ { a i + a j | (i ≤ n) (j ≤ n) } } (a (n + 1))) →
        let d := fun i ↦ a (i + 1) - a i
        ∃ p > 0, ∀ᶠ m in atTop, d (m + p) = d m

end Problem
