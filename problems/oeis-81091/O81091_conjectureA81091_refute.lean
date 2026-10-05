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

- problem_id: O81091_conjectureA81091_refute
- collection: oeis
- question_id: oeis:81091
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/81091.lean#conjectureA81091
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Conjecture (A81091)**: There are infinite primes of the form $2^n + 2^i + 1$, with $0 < i < n$.
- notes: OEIS A81091 -- https://oeis.org/A81091
- track: open
- answer_shape: refute
- pair_id: O81091_conjectureA81091
- pair_role: refute
- source_stem: 81091
- source_namespace: OeisA81091
- source_theorem: conjectureA81091
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_7 a_11 a_13 a_19 a_37
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Primes with $m$ one bits in their binary representation. -/
def isPrimeBitsSet (m p : ℕ) : Prop :=
  p.Prime ∧ p.bits.count true = m

/-- Primes in A81091 have exactly $3$ set bits in binary representation ($2^n + 2^i + 1$). -/
def A (p : ℕ) : Prop :=
  isPrimeBitsSet 3 p

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_7 : A 7 := by unfold A isPrimeBitsSet; decide +kernel

@[category test, AMS 11]
theorem a_11 : A 11 := by unfold A isPrimeBitsSet; decide +kernel

@[category test, AMS 11]
theorem a_13 : A 13 := by unfold A isPrimeBitsSet; decide +kernel

@[category test, AMS 11]
theorem a_19 : A 19 := by unfold A isPrimeBitsSet; decide +kernel

@[category test, AMS 11]
theorem a_37 : A 37 := by unfold A isPrimeBitsSet; decide +kernel

abbrev Target : Prop :=
    ¬ (
      Set.Infinite {p : ℕ | A p}
    )

end Problem
