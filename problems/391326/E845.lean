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

- problem_id: E845
- collection: erdos
- question_id: erdos:845
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/845.lean#erdos_845
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $C > 0$. Is it true that the set of integers of the form $n = b_1 + \cdots + b_t$, with $b_1 < \cdots < b_t$, where $b_i = 2^{k_i}3^{l_i}$ for $1 \leq i\leq t$ and $b_t \leq Cb_1$ has density $0$? van Doorn and Everts \cite{vDEv25} have disproved this with $C=6$ - in fact, they prove that all integers can be written as such a sum in which $b_t<6b_1$. This was formalized in Lean by Alexeev using Aristotle.
- notes: Erdos Problem 845 -- https://www.erdosproblems.com/845
- track: solved
- answer_shape: decide
- source_stem: 845
- mathdb_ref: erdos:845
- source_namespace: Erdos845
- source_theorem: erdos_845
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∀ᵉ (C : ℝ) (hC : 0 < C),
        let f : ℕ × ℕ → ℕ := fun (k, l) ↦ 2 ^ k * 3 ^ l
        { ∑ x ∈ B, f x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
          (hB : B.sup f ≤ C * B.inf' h f) }.HasDensity 0

end Problem
