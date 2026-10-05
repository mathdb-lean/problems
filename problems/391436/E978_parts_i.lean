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

- problem_id: E978_parts_i
- collection: erdos
- question_id: erdos:978
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/978.lean#erdos_978.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let `f ∈ ℤ[X]` be an irreducible polynomial with positive leading coefficient. Suppose that the degree `k` of `f` is larger than `2`, is not equal to a power of `2`, and `f n` has no fixed `(k - 1)`-th power divisors other than `1`. Then the set of `n` such that `f n` is `(k - 1)`-th power free has positive density, and this is proved in [Ho67].
- notes: Erdos Problem 978 -- https://www.erdosproblems.com/978
- track: solved
- answer_shape: proof
- source_stem: 978
- mathdb_ref: erdos:978
- source_namespace: Erdos978
- source_theorem: erdos_978.parts.i
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Polynomial Set

namespace Problem

abbrev Target : Prop :=
    ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 2 < f.natDegree)
        (hp2 : ∀ (x : ℕ), f.natDegree ≠ 2 ^ x) (hlc : 0 < f.leadingCoeff)
        (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ)),
      HasPosDensity {n : ℕ | Powerfree (f.natDegree - 1) (f.eval (n : ℤ))}

end Problem
