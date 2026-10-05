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

- problem_id: RDubner_dubner_conjecture
- collection: paper
- question_id: paper:Dubner
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/Dubner.lean#dubner_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Every even number greater than 4208 is the sum of two twin primes.
- notes: Problem from Dubner -- https://scispace.com/pdf/twin-prime-conjectures-3icaxy6b0m.pdf
- track: open
- answer_shape: proof
- source_stem: Dubner
- source_namespace: DubnerConjecture
- source_theorem: dubner_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: t1 t2 t3 t4 t5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
A twin prime is a prime number that has a prime gap of 2, meaning either p - 2 or p + 2
is also prime.
-/
def IsTwinPrime (p : ℕ) : Prop :=
  p.Prime ∧ ((p - 2).Prime ∨ (p + 2).Prime)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem t1 : ¬IsTwinPrime 2 := by
  norm_num [IsTwinPrime]

@[category test, AMS 11]
theorem t2 : IsTwinPrime 3 := by
  norm_num [IsTwinPrime]

@[category test, AMS 11]
theorem t3 : IsTwinPrime 5 := by
  norm_num [IsTwinPrime]

@[category test, AMS 11]
theorem t4 : IsTwinPrime 101 := by
  norm_num [IsTwinPrime]

@[category test, AMS 11]
theorem t5 : ¬IsTwinPrime 100 := by
  norm_num [IsTwinPrime]

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 4208 < n) (h : Even n),
      ∃ p q : ℕ,
        IsTwinPrime p ∧
        IsTwinPrime q ∧
        p + q = n

end Problem
