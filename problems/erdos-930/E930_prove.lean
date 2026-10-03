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

- problem_id: E930_prove
- collection: erdos
- question_id: erdos:930
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/930.lean#erdos_930
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for every $r$, there is a $k$ such that if $I_1,\ldots,I_r$ are disjoint intervals of consecutive integers, all of length at least $k$, then $$ \prod_{1\leq i\leq r}\prod_{m\in I_i}m $$ is not a perfect power?
- notes: Erdos Problem 930 -- https://www.erdosproblems.com/930
- track: open
- answer_shape: prove
- pair_id: E930
- pair_role: prove
- source_stem: 930
- mathdb_ref: erdos:930
- source_namespace: Erdos930
- source_theorem: erdos_930
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset

namespace Problem

/--
$n$ is a perfect power if there exist natural numbers $m$ and $l$
such that $1 < l$ and $m^l = n$.
-/
def IsPower (n : ℕ) : Prop :=
  ∃ m l, 1 < l ∧ m^l = n

/--
Returns the least prime satisfying $k \le p$
-/
def nextPrime (k : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes k)

abbrev Target : Prop :=
    ∀ r > 0, ∃ k, ∀ I₁ I₂ : Fin r → ℕ,
      (∀ i : Fin r, 0 < I₁ i ∧ I₁ i + k ≤ I₂ i + 1) →
        (∀ i j : Fin r, i < j → I₂ i < I₁ j) →
          ¬ IsPower (∏ i : Fin r, ∏ m ∈ Icc (I₁ i) (I₂ i), m)

end Problem
