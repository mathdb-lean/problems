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

- problem_id: E1105_parts_ii
- collection: erdos
- question_id: erdos:1105
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1105.lean#erdos_1105.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $P_k$ be the path on $k$ vertices and $\ell=\lfloor\frac{k-1}{2}\rfloor$. If $n\geq k\geq 5$ then is $\mathrm{AR}(n,P_k)$ equal to $\max\left(\binom{k-2}{2}+1, \binom{\ell-1}{2}+(\ell-1)(n-\ell+1)+\epsilon\right)$where $\epsilon=1$ if $k$ is odd and $\epsilon=2$ otherwise? A proof of the formula for $\mathrm{AR}(n,P_k)$ for all $n\geq k\geq 5$ has been announced by Yuan [Yu21].
- notes: Erdos Problem 1105 -- https://www.erdosproblems.com/1105
- track: solved
- answer_shape: decide
- source_stem: 1105
- mathdb_ref: erdos:1105
- source_namespace: Erdos1105
- source_theorem: erdos_1105.parts.ii
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open SimpleGraph Asymptotics Filter

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
        let ℓ := (k - 1) / 2
        let ε := if Odd k then 1 else 2
        antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 +
          (ℓ - 1) * (n - ℓ + 1) + ε)

end Problem
