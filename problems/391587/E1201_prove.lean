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

- problem_id: E1201_prove
- collection: erdos
- question_id: erdos:1201
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1201.lean#erdos_1201
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that for every $\epsilon,\eta>0$ there exists a $k$ such that the density of $n$ for which $P(n(n+1)\cdots(n+k))>n^{1-\epsilon}$ is at least $1-\eta$ (where $P(m)$ is the greatest prime divisor of $m$)?
- notes: Erdos Problem 1201 -- https://www.erdosproblems.com/1201
- track: open
- answer_shape: prove
- pair_id: E1201
- pair_role: prove
- source_stem: 1201
- mathdb_ref: erdos:1201
- source_namespace: Erdos1201
- source_theorem: erdos_1201
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter Finset

namespace Problem

/--
The set of $n$ for which $P(n(n+1)\cdots(n+k)) > n^{1-\epsilon}$, where $P(m)$ is the greatest prime
divisor of $m$.
-/
noncomputable def Erdos1201Set (ε : ℝ) (k : ℕ) : Set ℕ :=
  { n : ℕ |
    ((sSup {p : ℕ | p.Prime ∧ p ∣ ∏ i ∈ range (k + 1), (n + i)} : ℕ) : ℝ) > (n : ℝ) ^ (1 - ε) }

open scoped Classical in
abbrev Target : Prop :=
    ∀ ε > 0, ∀ η > 0, ∃ k : ℕ,
        atTop.liminf (fun x : ℕ ↦
          (((count (· ∈ Erdos1201Set ε k) x : ℝ) / (x : ℝ)) : EReal)) ≥ (1 - η : EReal)

end Problem
