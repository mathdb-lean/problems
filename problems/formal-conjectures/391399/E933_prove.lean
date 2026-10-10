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

- problem_id: E933_prove
- collection: erdos
- question_id: erdos:933
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/933.lean#erdos_933
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $n(n+1)=2^k3^lm$, where $(m,6)=1$, then is it true that $\limsup_{n\to \infty} \frac{2^k3^l}{n\log n}=\infty$?
- notes: Erdos Problem 933 -- https://www.erdosproblems.com/933
- track: open
- answer_shape: prove
- pair_id: E933
- pair_role: prove
- source_stem: 933
- mathdb_ref: erdos:933
- source_namespace: Erdos933
- source_theorem: erdos_933
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

/-- The 2-adic valuation of $n(n+1)$. -/
def k (n : ℕ) : ℕ := padicValNat 2 (n * (n + 1))

/-- The 3-adic valuation of $n(n+1)$. -/
def l (n : ℕ) : ℕ := padicValNat 3 (n * (n + 1))

abbrev Target : Prop :=
    atTop.limsup (fun n : ℕ ↦
        ((((2 ^ k n * 3 ^ l n : ℕ) : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) : EReal)) = ⊤

end Problem
