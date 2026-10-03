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

- problem_id: E1142_refute
- collection: erdos
- question_id: erdos:1142
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1142.lean#erdos_1142
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many $n > 2$ such that $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$? The only known such $n$ are $4, 7, 15, 21, 45, 75, 105$ (OEIS [A039669](https://oeis.org/A039669)).
- notes: Erdos Problem 1142 -- https://www.erdosproblems.com/1142
- track: open
- answer_shape: refute
- pair_id: E1142
- pair_role: refute
- source_stem: 1142
- mathdb_ref: erdos:1142
- source_namespace: Erdos1142
- source_theorem: erdos_1142
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Set

namespace Problem

/--
The property that $n > 2$ and $n - 2^k$ is prime for all $k \geq 1$ with $2^k < n$.

Following the OEIS [A039669](https://oeis.org/A039669) convention ("Numbers n > 2 such that ..."),
we require $n > 2$ to exclude the trivial cases $n \leq 2$, for which the primality condition
is vacuously satisfied.
-/
def Erdos1142Prop (n : ℕ) : Prop :=
  2 < n ∧ ∀ k, 0 < k → 2 ^ k < n → (n - 2 ^ k).Prime

local macro "prove_erdos_1142_prop" bound:num : tactic =>
  `(tactic| (
    refine ⟨by omega, fun k hk hlt => ?_⟩
    have : k ≤ $bound := by
      by_contra! h
      exact absurd (Nat.pow_le_pow_right (by omega : 1 ≤ 2) h) (by omega)
    interval_cases k <;> simp_all (config := { decide := true })))

abbrev Target : Prop :=
    ¬ (
      Infinite { n | Erdos1142Prop n }
    )

end Problem
