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

- problem_id: E818
- collection: erdos
- question_id: erdos:818
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/818.lean#erdos_818
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be a finite set of integers such that $\lvert A+A\rvert \ll \lvert A\rvert$. Is it true that $$\lvert AA\rvert \gg \frac{\lvert A\rvert^2}{(\log \lvert A\rvert)^C}$$ for some constant $C>0$? This was proved by Solymosi [So09d], in the strong form $$\lvert AA\rvert \gg \frac{\lvert A\rvert^2}{\log \lvert A\rvert}.$$ See also [52].
- notes: Erdos Problem 818 -- https://www.erdosproblems.com/818
- track: solved
- answer_shape: decide
- source_stem: 818
- mathdb_ref: erdos:818
- source_namespace: Erdos818
- source_theorem: erdos_818
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped Pointwise

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
          ∀ A : Finset ℤ, 2 ≤ A.card → ((A + A).card : ℝ) ≤ K * (A.card : ℝ) →
            c * (A.card : ℝ) ^ 2 / (Real.log (A.card : ℝ)) ^ C ≤ ((A * A).card : ℝ)

end Problem
