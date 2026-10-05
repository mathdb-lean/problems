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

- problem_id: NPolyTimeFunctions_isPolyTime_primeFactorsList_refute
- collection: wikipedia
- question_id: wikipedia:PolyTimeFunctions
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/PolyTimeFunctions.lean#isPolyTime_primeFactorsList
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **The integer factorization problem**: Can the prime factorization of a positive integer be computed in polynomial time? We state the problem by asking if `Nat.primeFactorsList` is polynomial-time computable (assuming typical encodings of ℕ and List ℕ into bitstrings). *Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Integer_factorization)
- notes: Wikipedia: PolyTimeFunctions -- https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_computer_science
- track: open
- answer_shape: refute
- pair_id: NPolyTimeFunctions_isPolyTime_primeFactorsList
- pair_role: refute
- source_stem: PolyTimeFunctions
- source_namespace: PolyTime
- source_theorem: isPolyTime_primeFactorsList
- source_category: research open
- source_ams: 68
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open ComplexityTheory

abbrev Target : Prop :=
    ¬ (
      IsPolyTime Nat.primeFactorsList
    )

end Problem
