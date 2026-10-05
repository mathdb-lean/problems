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

- problem_id: NBunyakovsky_bunyakovsky_conjecture
- collection: wikipedia
- question_id: wikipedia:Bunyakovsky
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/Bunyakovsky.lean#bunyakovsky_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Bunyakovsky conjecture** If a polynomial $f$ over integers satisfies both Schinzel and Bunyakovsky conditions, there exist infinitely many natural numbers $m$ such that $f(m)$ is prime.
- notes: Wikipedia: Bunyakovsky -- https://en.wikipedia.org/wiki/Bunyakovsky_conjecture
- track: open
- answer_shape: proof
- source_stem: Bunyakovsky
- source_namespace: Bunyakovsky
- source_theorem: bunyakovsky_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Polynomial

namespace Problem

abbrev Target : Prop :=
    ∀ (f : ℤ[X]),
      BunyakovskyCondition f ∧ SchinzelCondition {f} →
      Infinite {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}

end Problem
