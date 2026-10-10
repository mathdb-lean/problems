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

- problem_id: E384
- collection: erdos
- question_id: erdos:384
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/384.lean#erdos_384
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $1<k<n-1$ then $\binom{n}{k}$ is divisible by a prime $p\leq n/2$ (except $\binom{7}{3}=\binom{7}{4}=5\cdot 7$). A conjecture of Erdős and Selfridge [ErGr80]. Proved by Ecklund [Ec69], who made the stronger conjecture that whenever $n>k^2$ the binomial coefficient $\binom{n}{k}$ is divisible by a prime $p<n/k$. Discussed in problem B31 and B33 of Guy's collection [Gu04]. Stronger forms of this conjecture are [1094](https://www.erdosproblems.com/1094) and [1095](https://www.erdosproblems.com/1095). Ecklund's theorem is stated for $n \geq 2k$ with the single exception $\binom{7}{3}$; by the symmetry $\binom{n}{k} = \binom{n}{n-k}$ this is the form above, where $\binom{7}{4}$ is the second exception. The prime bound is $p \leq n/2$ (that is, $2p \leq n$); see `erdos_384.variants.strict` for the strict inequality.
- notes: Erdos Problem 384 -- https://www.erdosproblems.com/384
- track: solved
- answer_shape: proof
- source_stem: 384
- mathdb_ref: erdos:384
- source_namespace: Erdos384
- source_theorem: erdos_384
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3))
        (h₄ : (n, k) ≠ (7, 4)),
      ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n

end Problem
