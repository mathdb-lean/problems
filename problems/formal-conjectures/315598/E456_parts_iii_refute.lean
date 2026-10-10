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

- problem_id: E456_parts_iii_refute
- collection: erdos
- question_id: erdos:456
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/456.lean#erdos_456.parts.iii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many primes $p$ such that $p-1$ is the only $n$ for which $m_n=p$?
- notes: Erdos Problem 456 -- https://www.erdosproblems.com/456
- track: open
- answer_shape: refute
- pair_id: E456_parts_iii
- pair_role: refute
- source_stem: 456
- mathdb_ref: erdos:456
- source_namespace: Erdos456
- source_theorem: erdos_456.parts.iii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter
open scoped Topology Asymptotics

namespace Problem

/--
Let $p_n$ be the smallest prime $\equiv 1\pmod{n}$.
-/
noncomputable def p (n : ℕ) : ℕ :=
  sInf { k | k.Prime ∧ k ≡ 1 [MOD n] }

/--
Let $m_n$ be the smallest integer such that $n\mid \phi(m_n)$.
-/
noncomputable def m (n : ℕ) : ℕ :=
  sInf { k | 0 < k ∧ n ∣ totient k }

abbrev Target : Prop :=
    ¬ (
      { q | q.Prime ∧ ∀ n, m n = q ↔ n = q - 1 }.Infinite
    )

end Problem
