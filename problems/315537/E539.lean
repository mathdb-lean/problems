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

- problem_id: E539
- collection: erdos
- question_id: erdos:539
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/539.lean#erdos_539
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $h(n)$ be maximal such that, for any set $A\subseteq \mathbb{N}$ of size $n$, the set$$\left\{ \frac{a}{(a,b)}: a,b\in A\right\}$$has size at least $h(n)$. Estimate $h(n)$.
- notes: Erdos Problem 539 -- https://www.erdosproblems.com/539
- track: open
- answer_shape: value
- answer_type: ℕ → ℝ
- answer_pinned: false
- answer_pinned_reason: relation_is_reflexive
- source_stem: 539
- mathdb_ref: erdos:539
- source_namespace: Erdos539
- source_theorem: erdos_539
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

open scoped Asymptotics Finset

namespace Problem

/-- We say that $m$ is a cofactor lower bound for a given $n$ if, for every set $A$ of $n$
non-negative integers, there are at least $m$ cofactors $a / (a, b)$, where $a, b\in A$.-/
def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, #A = n →
  m ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b)

/-- The cofactor threshold $h(n)$, for every positive $n$, is the largest cofactor lower bound
for $n$. -/
noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

abbrev Target (value : ℕ → ℝ) : Prop :=
    (fun n ↦ (cofactorThreshold n : ℝ)) =Θ[atTop] value

end Problem
