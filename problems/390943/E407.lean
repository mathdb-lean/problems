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

- problem_id: E407
- collection: erdos
- question_id: erdos:407
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/407.lean#erdos_407
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $w(n)$ count the number of solutions to $$n=2^a+3^b+2^c3^d$$ with $a,b,c,d\geq 0$ integers. Is it true that $w(n)$ is bounded by some absolute constant? A conjecture originally due to Newman. This is true, and was proved by Evertse, Győry, Stewart, and Tijdeman [EGST88]. Quantitative bounds were provided by Tijdeman and Wang [TiWa88], who proved that (if $w(n)$ only counts distinct solutions, where we call two solutions distinct if the sets $\{2^a,3^b,2^{c}3^d\}$ are distinct) then $w(n) \leq 4$ for all large $n$. This was made effective by Bajpai and Bennett [BaBe24], who proved that $w(n)\leq 4$ if $n\geq 131082$ and $w(n)\leq 9$ for all $n$. (The largest $n$ for which $w(n)=9$ is $299$.)
- notes: Erdos Problem 407 -- https://www.erdosproblems.com/407
- track: solved
- answer_shape: decide
- source_stem: 407
- mathdb_ref: erdos:407
- source_namespace: Erdos407
- source_theorem: erdos_407
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- `w n` counts the ordered quadruples $(a,b,c,d)$ of nonnegative integers with
$n=2^a+3^b+2^c3^d$. -/
noncomputable def w (n : ℕ) : ℕ :=
  {x : ℕ × ℕ × ℕ × ℕ | 2 ^ x.1 + 3 ^ x.2.1 + 2 ^ x.2.2.1 * 3 ^ x.2.2.2 = n}.ncard

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ C : ℕ, ∀ n : ℕ, w n ≤ C

end Problem
