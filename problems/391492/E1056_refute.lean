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

- problem_id: E1056_refute
- collection: erdos
- question_id: erdos:1056
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1056.lean#erdos_1056
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k ≥ 2$. Does there exist a prime $p$ and consecutive intervals $I_0,\dots,I_k$ such that $\prod\limits_{n{\in}I_i}n \equiv 1 \mod n$ for all $1 \le i \le k$?
- notes: Erdos Problem 1056 -- https://www.erdosproblems.com/1056
- track: open
- answer_shape: refute
- pair_id: E1056
- pair_role: refute
- source_stem: 1056
- mathdb_ref: erdos:1056
- source_namespace: Erdos1056
- source_theorem: erdos_1056
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat

namespace Problem

/--
The proposition that the modular product of a collection of consecutive interval equals $1$ modulo $p$,
where intervals are defined by a function specifying the consecutive boundaries.
-/
def AllModProdEqualsOne (p : ℕ) {k : ℕ} (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

abbrev Target : Prop :=
    ¬ (
      ∀ k ≥ 2, ∃ (p : ℕ) (_ : p.Prime) (boundaries : Fin (k + 1) → ℕ) (_ : StrictMono boundaries),
          AllModProdEqualsOne p boundaries
    )

end Problem
