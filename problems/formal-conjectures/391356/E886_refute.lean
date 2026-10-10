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

- problem_id: E886_refute
- collection: erdos
- question_id: erdos:886
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/886.lean#erdos_886
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\epsilon>0$. Is it true that, for all large $n$, the number of divisors of $n$ in $(n^{1/2},n^{1/2}+n^{1/2-\epsilon})$ is $O_\epsilon(1)$? Erdős attributes this conjecture to Ruzsa.
- notes: Erdos Problem 886 -- https://www.erdosproblems.com/886
- track: open
- answer_shape: refute
- pair_id: E886
- pair_role: refute
- source_stem: 886
- mathdb_ref: erdos:886
- source_namespace: Erdos886
- source_theorem: erdos_886
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter

namespace Problem

/--
The set of divisors of $n$ in the interval $(n^{1/2}, n^{1/2} + n^{1/2-\epsilon})$.
-/
noncomputable def Erdos886Divisors (n : ℕ) (ε : ℝ) (C : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d =>
    (n : ℝ) ^ (1/2 : ℝ) < d ∧ (d : ℝ) < (n : ℝ) ^ (1/2 : ℝ) + C * (n : ℝ) ^ (1/2 - ε))

abbrev Target : Prop :=
    ¬ (
      ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in atTop, (Erdos886Divisors n ε 1).card ≤ K
    )

end Problem
