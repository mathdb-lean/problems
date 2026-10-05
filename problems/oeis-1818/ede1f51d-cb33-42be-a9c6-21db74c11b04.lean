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

- problem_id: O1818_conjecture1
- collection: oeis
- question_id: oeis:1818
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/1818.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture 1: For any primitive $2n$-th root $\zeta$ of unity, the permanent of the $2n \times 2n$ matrix $[m(j,k)]_{j,k=1..2n}$ coincides with $a(n) = ((2n-1)!!)^2$, where $m(j,k)$ is $(1+\zeta^{j-k})/(1-\zeta^{j-k})$ if $j \neq k$, and $1$ otherwise. - Zhi-Wei Sun, Dec 21 2021
- notes: OEIS A1818 -- https://oeis.org/A1818
- track: solved
- answer_shape: proof
- source_stem: 1818
- source_namespace: OeisA1818
- source_theorem: conjecture1
- source_category: research solved
- source_ams: 11 15
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The sequence of squares of double factorials: $a(n) = ((2n-1)!!)^2$. -/
def a (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n, (2 * k + 1)) ^ 2

/-- Characteristic function $f(j, k)$ for matrix entries in $\mathbb{Z}/p^2\mathbb{Z}$. -/
noncomputable def fEntry {p : ℕ} (i j : ℕ) : ZMod (p ^ 2) :=
  let R := ZMod (p ^ 2)
  if i = j then
    1
  else
    let iInt : ℤ := i
    let jInt : ℤ := j
    let num : R := (iInt + jInt : ℤ)
    let den : R := (iInt - jInt : ℤ)
    num * den⁻¹

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
theorem a_2 : a 2 = 9 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 225 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 11025 := by decide

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 1 ≤ n),
      ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
        Matrix.permanent (fun (i j : Fin (2 * n)) =>
          if i = j then
            (1 : ℂ)
          else
            (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
        ) = (a n : ℂ)

end Problem
