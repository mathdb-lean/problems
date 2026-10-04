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

- problem_id: E1093_parts_ii
- collection: erdos
- question_id: erdos:1093
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1093.lean#erdos_1093.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there only finitely many binomial coefficients with deficiency > 1?
- notes: Erdos Problem 1093 -- https://www.erdosproblems.com/1093
- track: open
- answer_shape: proof
- source_stem: 1093
- mathdb_ref: erdos:1093
- source_namespace: Erdos1093
- source_theorem: erdos_1093.parts.ii
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Finset Nat

/--
If defined, the deficiency is the count of $0 \le i < k$ such that $n - i$ is $k$-smooth,
that is, divisible only by primes $\le k$.

`Nat.smoothNumbers m` is the set of positive naturals all of whose prime factors are
$< m$, so "$k$-smooth" in the sense above is `Nat.smoothNumbers (k + 1)`.
-/
noncomputable def deficiency (n k : ℕ) : ℕ :=
  #{i ∈ range k | n - i ∈ smoothNumbers (k + 1)}

abbrev Target : Prop :=
    {x : ℕ × ℕ | let k := x.1; let n := x.2; 2 * k ≤ n ∧ deficiency n k > 1 ∧
      ∀ p, p.Prime → (p ∣ choose n k) → k < p}.Finite

end Problem
