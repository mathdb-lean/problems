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

- problem_id: E403
- collection: erdos
- question_id: erdos:403
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/403.lean#erdos_403
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does the equation $$2^m=a_1!+\cdots+a_k!$$ with $a_1<a_2<\cdots <a_k$ have only finitely many solutions? Asked by Burr and Erdős. Frankl and Lin [Li76] independently showed that the answer is yes, and the largest solution is $$2^7=2!+3!+5!.$$ In fact Lin showed that the largest power of $2$ which can divide a sum of distinct factorials containing $2$ is $2^{254}$, and that there are only 5 solutions to $3^m=a_1!+\cdots+a_k!$ (when $m=0,1,2,3,6$). See also [404]. A solution is encoded below as a pair $(m, s)$ where $s$ is the finite set $\{a_1 < a_2 < \cdots < a_k\}$ of positive integers, so the distinctness of the $a_i$ is given by set membership. The empty set contributes no solutions since $2^m \geq 1 > 0$. The linked proof gives more than finiteness: it classifies the solutions outright, as $(0,\{1\})$, $(1,\{2\})$, $(3,\{2,3\})$, $(5,\{2,3,4\})$ and $(7,\{2,3,5\})$, so the set below has exactly five elements.
- notes: Erdos Problem 403 -- https://www.erdosproblems.com/403
- track: solved
- answer_shape: decide
- source_stem: 403
- mathdb_ref: erdos:403
- source_namespace: Erdos403
- source_theorem: erdos_403
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        {p : ℕ × Finset ℕ | (∀ a ∈ p.2, 0 < a) ∧
          2 ^ p.1 = ∑ a ∈ p.2, a.factorial}.Finite

end Problem
