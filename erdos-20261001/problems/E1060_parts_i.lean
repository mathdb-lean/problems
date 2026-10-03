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

- problem_id: E1060_parts_i
- collection: erdos
- question_id: erdos:1060
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1060.lean#erdos_1060.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The conjecture is about the function $f(n)$ which counts the number of solutions to $k\sigma(k)=n$, where $\sigma(k)$ is the sum of divisors of $k$. The first bound is that $f(n)$ grows slower than any power of $n^(\frac{1}{\log\log n})$. The second bound is that $f(n)$ is at most a power of $\log n$.
- notes: Erdos Problem 1060 -- https://www.erdosproblems.com/1060
- track: open
- answer_shape: proof
- source_stem: 1060
- mathdb_ref: erdos:1060
- source_namespace: Erdos1060
- source_theorem: erdos_1060.parts.i
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Asymptotics Finset Filter Real
open scoped ArithmeticFunction.sigma

namespace Problem

abbrev Target : Prop :=
    ∃ h : ℕ → ℝ,
      h =o[atTop] (fun n ↦ 1 / log (log n)) ∧ ∀ᶠ n in atTop, #{k ≤ n | k * σ 1 k = n} ≤ (n : ℝ) ^ h n

end Problem
