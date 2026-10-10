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

- problem_id: E459
- collection: erdos
- question_id: erdos:459
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/459.lean#erdos_459
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(u)$ be the largest $v$ such that no $m\in (u,v)$ is composed entirely of primes dividing $uv$. Estimate $f(u)$. The estimate $u + 2 \le f(u) \le u^2$ holds for every $u \ge 2$. The upper bound is attained when $u$ is prime, and the lower bound when $u = 2^k - 2$ with $k \ge 2$; Cambie further showed that $f(n) = (1 + o(1))n$ for almost all $n$.
- notes: Erdos Problem 459 -- https://www.erdosproblems.com/459
- track: solved
- answer_shape: proof
- source_stem: 459
- mathdb_ref: erdos:459
- source_namespace: Erdos459
- source_theorem: erdos_459
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The function from the problem, in its equivalent form: `f u` is the smallest `v > u` all of whose
prime factors divide `u`. (Equivalently, `f u` is the largest `v` such that no `m ∈ (u, v)` is
composed entirely of primes dividing `u * v`.)
-/
noncomputable def f (u : ℕ) : ℕ := sInf {v | u < v ∧ v.primeFactors ⊆ u.primeFactors}

abbrev Target : Prop :=
    ∀ {u : ℕ} (hu : 2 ≤ u),
      u + 2 ≤ f u ∧ f u ≤ u ^ 2

end Problem
