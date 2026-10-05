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

- problem_id: NFeitThompsonPrimeConjecture_feit_thompson_primes
- collection: wikipedia
- question_id: wikipedia:FeitThompsonPrimeConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/FeitThompsonPrimeConjecture.lean#feit_thompson_primes
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There are no distinct primes $p$ and $q$ such that $\frac{q^p - 1}{q - 1}$ divides $\frac{p^q - 1}{p - 1}$
- notes: Wikipedia: FeitThompsonPrimeConjecture -- https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_conjecture
- track: open
- answer_shape: proof
- source_stem: FeitThompsonPrimeConjecture
- source_namespace: FeitThompsonPrimeConjecture
- source_theorem: feit_thompson_primes
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p < q),
      ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)

end Problem
