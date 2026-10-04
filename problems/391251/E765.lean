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

- problem_id: E765
- collection: erdos
- question_id: erdos:765
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/765.lean#erdos_765
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Give an asymptotic formula for $\mathrm{ex}(n; C_4)$. Erdős and Klein [Er38] proved $\mathrm{ex}(n; C_4) \asymp n^{3/2}$, and Reiman [Re58] proved $$\frac{1}{2\sqrt 2} \le \lim \frac{\mathrm{ex}(n; C_4)}{n^{3/2}} \le \frac12.$$ Erdős and Rényi [ERS66], and independently Brown [Br66], gave a construction showing that if $n = q^2 + q + 1$ with $q$ a prime power then $\mathrm{ex}(n; C_4) \ge \frac12 q (q+1)^2$; together with Reiman's upper bound this gives $\mathrm{ex}(n; C_4) \sim \frac12 n^{3/2}$. Füredi [Fu83] proved $\mathrm{ex}(n; C_4) = \frac12 q (q+1)^2$ for $q > 13$.
- notes: Erdos Problem 765 -- https://www.erdosproblems.com/765
- track: solved
- answer_shape: proof
- source_stem: 765
- mathdb_ref: erdos:765
- source_namespace: Erdos765
- source_theorem: erdos_765
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Asymptotics

namespace Problem

abbrev Target : Prop :=
    (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ)) ~[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ) / 2

end Problem
