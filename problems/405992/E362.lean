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

- problem_id: E362
- collection: erdos
- question_id: erdos:362
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/362.lean#erdos_362
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{N}$ be a finite set of size $N$. Is it true that, for any fixed $t$, there are $$\ll \frac{2^N}{N^{3/2}}$$ many $S\subseteq A$ such that $\sum_{n\in S}n=t$? Erdős and Moser [Er65] proved the first bound with an additional factor of $(\log n)^{3/2}$. This was removed by Sárközy and Szemerédi [SaSz65], thereby answering the first question in the affirmative. Stanley [St80] has shown that this quantity is maximised when $A=\{-\lfloor \frac{N-1}{2}\rfloor,\ldots,\lfloor\frac{N}{2}\rfloor\}$.
- notes: Erdos Problem 362 -- https://www.erdosproblems.com/362
- track: solved
- answer_shape: decide
- source_stem: 362
- mathdb_ref: erdos:362
- source_namespace: Erdos362
- source_theorem: erdos_362
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ C : ℝ, ∀ (A : Finset ℕ) (t : ℕ), A.Nonempty →
        ({S ∈ A.powerset | ∑ n ∈ S, n = t}.card : ℝ) ≤ C * 2 ^ A.card / (A.card : ℝ) ^ (3 / 2 : ℝ)

end Problem
