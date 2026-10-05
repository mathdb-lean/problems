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

- problem_id: M339137
- collection: mathoverflow
- question_id: mathoverflow:339137
- source: formal-conjectures
- source_locator: FormalConjectures/Mathoverflow/339137.lean#mathoverflow_339137
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $P(x), Q(x) ∈ ℝ[x]$ be two monic polynomials with non-negative coefficients. If $R(x) = P(x)Q(x)$ is a $0,1$ polynomial (coefficients only from $\{0,1\}$), then $P(x)$ and $Q(x)$ are also $0, 1$ polynomials.
- notes: MathOverflow 339137 -- https://mathoverflow.net/questions/339137
- track: open
- answer_shape: proof
- source_stem: 339137
- source_namespace: Mathoverflow339137
- source_theorem: mathoverflow_339137
- source_category: research open
- source_ams: 12
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Polynomial

namespace Problem

/--
The predicate that all coefficients of a polynomial are either zero or one.
`P.coeffs` is the finite set of all *nonzero* coefficients of the polynomial `P`.
So `IsZeroOne P` means that every nonzero coefficient of `P` is equal to 1.
Note that zero coefficients are not included in `P.coeffs`.
-/
def IsZeroOne (P : ℝ[X]) := P.coeffs ⊆ {1}

abbrev Target : Prop :=
    ∀ (P Q R : ℝ[X]) (hP: P.Monic) (hQ : Q.Monic)
        (hp : ∀ c ∈ P.coeffs, 0 ≤ c) (hq : ∀ c ∈ Q.coeffs, 0 ≤ c)
        (h : R = P * Q) (hR : IsZeroOne R),
      IsZeroOne P ∧ IsZeroOne Q

end Problem
