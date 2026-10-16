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

- problem_id: NAgrawal_agrawal_conjecture_refute
- collection: wikipedia
- question_id: wikipedia:Agrawal
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/Agrawal.lean#agrawal_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Agrawal's Primality Conjecture.** Does the congruence $(X-1)^n \equiv X^n - 1 \pmod{n, X^r-1}$ imply $n$ is prime (with a specific exception for $n^2 \equiv 1 \pmod{r}$)? While the "if" direction is a known theorem, the "only if" direction remains a conjecture.
- notes: Wikipedia: Agrawal -- https://en.wikipedia.org/wiki/Agrawal%27s_conjecture
- track: open
- answer_shape: refute
- pair_id: NAgrawal_agrawal_conjecture
- pair_role: refute
- source_stem: Agrawal
- source_namespace: AgrawalConjecture
- source_theorem: agrawal_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Polynomial

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ (n r : ℕ), n > 1 → r > 0 → n.gcd r = 1 →
          let R := Polynomial (ZMod n)
          let X : R := Polynomial.X
          let I : Ideal R := Ideal.span ({X^r - 1} : Set R)
          Ideal.Quotient.mk I ((X - 1)^n) = Ideal.Quotient.mk I (X^n - 1) →
          (n.Prime ∨ (n^2 : ZMod r) = 1)
    )

end Problem
