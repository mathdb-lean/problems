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

- problem_id: O71524_conjecture1
- collection: oeis
- question_id: oeis:71524
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/71524.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: $a(n) = 0$ for no $n > 28$. - _Zhi-Wei Sun_, Aug 26 2013
- notes: OEIS A71524 -- https://oeis.org/A71524
- track: open
- answer_shape: proof
- source_stem: 71524
- source_namespace: OeisA71524
- source_theorem: conjecture1
- source_category: research open
- source_ams: 11 15
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Matrix

/-- Determinant of the $n \times n$ matrix with $(i,j)$ entry $1$ if $(i+1)^2 + (j+1)^2$ is prime,
and $0$ otherwise. -/
def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_idx : ℕ := i.val + 1
    let j_idx : ℕ := j.val + 1
    if (i_idx ^ 2 + j_idx ^ 2).Prime then 1 else 0
  M.det

/-- Determinant of the $n \times n$ matrix with $(i,j)$ entry $1$
if $(i+1)^{2^m} + (j+1)^{2^m}$ is prime, and $0$ otherwise. -/

def generalDet (m n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_idx : ℕ := i.val + 1
    let j_idx : ℕ := j.val + 1
    if (i_idx ^ (2 ^ m) + j_idx ^ (2 ^ m)).Prime then 1 else 0
  M.det

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = -1 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  decide +kernel

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  decide +kernel

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 28 < n),
      a n ≠ 0

end Problem
