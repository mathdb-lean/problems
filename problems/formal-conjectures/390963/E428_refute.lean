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

- problem_id: E428_refute
- collection: erdos
- question_id: erdos:428
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/428.lean#erdos_428
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a set $A\subseteq \mathbb{N}$ such that, for infinitely many $n$, all of $n-a$ are prime for all $a\in A$ with $0 < a < n$ and $$\liminf\frac{\lvert A\cap [1,x]\rvert}{\pi(x)}>0?$$
- notes: Erdos Problem 428 -- https://www.erdosproblems.com/428
- track: open
- answer_shape: refute
- pair_id: E428
- pair_role: refute
- source_stem: 428
- mathdb_ref: erdos:428
- source_namespace: Erdos428
- source_theorem: erdos_428
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter Set

namespace Problem

/--
The density ratio of set $A$ up to $n$ relative to the prime counting function $\pi(n)$.
-/
noncomputable def primeDensityRatio (A : Set ℕ) (n : ℕ) : ℝ :=
  (A ∩ Icc 1 n).ncard / (primeCounting n)

abbrev Target : Prop :=
    ¬ (
      ∃ A : Set ℕ,
        (∃ᶠ n in atTop, ∀ a ∈ A, 0 < a → a < n → (n - a).Prime) ∧
        liminf (fun n ↦ primeDensityRatio A n) atTop > 0
    )

end Problem
