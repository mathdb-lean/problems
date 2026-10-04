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

- problem_id: E912
- collection: erdos
- question_id: erdos:912
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/912.lean#erdos_912
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Prove that there exists some $c>0$ such that $$h(n) \sim c \left(\frac{n}{\log n}\right)^{1/2}$$ as $n\to \infty$.
- notes: Erdos Problem 912 -- https://www.erdosproblems.com/912
- track: open
- answer_shape: proof
- source_stem: 912
- mathdb_ref: erdos:912
- source_namespace: Erdos912
- source_theorem: erdos_912
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Nat Asymptotics
open Filter

namespace Problem

/-- If $n! = \prod_{i}p_i^{k_i}$ is the factorization into distinct primes, then we define $h(n)$
to be the number of distinct exponents $k_i$. -/
noncomputable def h (n : ℕ) : ℕ := (n !).factorization.frange.card

abbrev Target : Prop :=
    ∃ c > 0,
        (fun n => (h n : ℝ)) ~[atTop] (fun n => c * (n / Real.log n) ^ (1 / 2 : ℝ))

end Problem
