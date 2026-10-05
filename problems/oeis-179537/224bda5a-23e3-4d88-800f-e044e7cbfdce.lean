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

- problem_id: O179537_conjecture4
- collection: oeis
- question_id: oeis:179537
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/179537.lean#conjecture4
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: $\sum_{k=0}^{p-1} (42k + 37) (-1)^k a(k) \equiv p(21(p/7) + 16) \pmod{p^2}$ for any prime $p \ne 7$. - _Zhi-Wei Sun_, Jul 17 2010
- notes: OEIS A179537 -- https://oeis.org/A179537
- track: open
- answer_shape: proof
- source_stem: 179537
- source_namespace: OeisA179537
- source_theorem: conjecture4
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The sequence $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}^2 (-16)^k$. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) ^ 2 * ((n - k).choose k : ℤ) ^ 2 * (-16 : ℤ) ^ k

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = -63 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = -575 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6913 := by decide

abbrev Target : Prop :=
    ∀ (p : ℕ) [Fact p.Prime] (_hp7 : p ≠ 7),
      letI : Fact (Nat.Prime 7) := ⟨by decide⟩
      (∑ k ∈ Finset.range p, ((42 * (k : ℤ) + 37) * (-1 : ℤ) ^ k * a k)) ≡
        (p : ℤ) * (21 * legendreSym 7 p + 16) [ZMOD (p : ℤ) ^ 2]

end Problem
