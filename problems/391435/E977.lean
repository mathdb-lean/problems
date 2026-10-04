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

- problem_id: E977
- collection: erdos
- question_id: erdos:977
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/977.lean#erdos_977
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $P(m)$ is the greatest prime divisor of $m$, then is it true that $$\frac{P(2^n-1)}{n}\to \infty$$ as $n\to \infty$? Schinzel [Sc62] proved that $P(2^n-1)>2n$ for $n>12$. In [Er65b] Erdős also asks about $P(n!+1)$. Stewart [St74b] proved that this conjecture is true if we restrict $n$ to those integers with $<\frac{1}{\log 2}\log\log n$ many prime factors. This was proved in the affirmative by Stewart [St13], who proved that $P(2^n-1)\gg n^{1+\frac{1}{104\log\log n}}$ for all large $n$.
- notes: Erdos Problem 977 -- https://www.erdosproblems.com/977
- track: solved
- answer_shape: decide
- source_stem: 977
- mathdb_ref: erdos:977
- source_namespace: Erdos977
- source_theorem: erdos_977
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        Tendsto (fun n : ℕ ↦ (Nat.maxPrimeFac (2 ^ n - 1) : ℝ) / n) atTop atTop

end Problem
