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

- problem_id: O34694_conjecture
- collection: oeis
- question_id: oeis:34694
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/34694.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: "Conjecture: $a(n) < n^2$ for $n > 1$. - _Thomas Ordowski_, Dec 19 2016"
- notes: OEIS A34694 -- https://oeis.org/A34694
- track: open
- answer_shape: proof
- source_stem: 34694
- source_namespace: OeisA34694
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Smallest prime $\equiv 1 \pmod n$. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ n ∣ (p - 1)}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := IsLeast.csInf_eq <| by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := IsLeast.csInf_eq <| by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 7 := IsLeast.csInf_eq <| by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 5 := IsLeast.csInf_eq <| by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 11 := IsLeast.csInf_eq <| by decide

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 1 < n),
      a n < n ^ 2

end Problem
