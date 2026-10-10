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

- problem_id: E32_prove
- collection: erdos
- question_id: erdos:32
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/32.lean#erdos_32
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist a set $A \subseteq \mathbb{N}$ such that $|A \cap \{1, \ldots, N\}| = o((\log N)^2)$ and every sufficiently large integer can be written as $p + a$ for some prime $p$ and $a \in A$?
- notes: Erdos Problem 32 -- https://www.erdosproblems.com/32
- track: open
- answer_shape: prove
- pair_id: E32
- pair_role: prove
- source_stem: 32
- mathdb_ref: erdos:32
- source_namespace: Erdos32
- source_theorem: erdos_32
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open scoped Nat
open Filter Set Asymptotics

/-- A set $A \subseteq \mathbb{N}$ is an _additive complement to the primes_ if every sufficiently
large natural number can be written as $p + a$ for some prime $p$ and $a \in A$. -/
def IsAdditiveComplementToPrimes (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a

open scoped Classical in
abbrev Target : Prop :=
    ∃ A : Set ℕ,
        IsAdditiveComplementToPrimes A ∧
        (fun N => (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) =o[atTop]
          fun N => (Real.log N) ^ 2

end Problem
