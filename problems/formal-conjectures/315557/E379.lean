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

- problem_id: E379
- collection: erdos
- question_id: erdos:379
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/379.lean#erdos_379
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $S(n)$ denote the largest integer such that, for all $1 ≤ k < n$, the binomial coefficient $\binom{n}{k}$ is divisible by $p^S(n)$ for some prime $p$ (depending on $k$).Then $\limsup S(n) = \infty$. This was formalized in Lean by Tao.
- notes: Erdos Problem 379 -- https://www.erdosproblems.com/379
- track: solved
- answer_shape: proof
- source_stem: 379
- mathdb_ref: erdos:379
- source_namespace: Erdos379
- source_theorem: erdos_379
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter

noncomputable def S (n : ℕ) : ℕ :=
  sSup {s | ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^s ∣n.choose k}

abbrev Target : Prop :=
    atTop.limsup (fun n => (S n : ℕ∞)) = ⊤

end Problem
