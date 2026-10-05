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

- problem_id: O100478_conjecture
- collection: oeis
- question_id: oeis:100478
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/100478.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Starting with other values of $a(1)$, $a(2)$, $a(3)$, $a(4)$, $a(5)$ what behaviors are possible? Does the sequence always stick at a single integer after some point, or can it go into a loop, or is there a third pattern? KitaKen1 showed the sequence either becomes constant or goes into a loop, see https://github.com/KitaKen1/oeis-a100478-eventual-periodicity/blob/642eed0ffee26415528ab8c48c5181826be04860/lean/OeisA100478FC.lean#L158-L168. tadamcz showed the sequence always becomes constant, see https://tadamcz.com/fc-review-results/aea251bb26/#/f/OEIS/100478.
- notes: OEIS A100478 -- https://oeis.org/A100478
- track: solved
- answer_shape: decide
- source_stem: 100478
- source_namespace: OeisA100478
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open scoped Nat.Prime

/--
The primary defining sequence `a`.
Pentanacci $\pi$ sequence: $a(1)=a(2)=a(3)=a(4)=a(5)=1$;
for $n>5$, $a(n) = \pi(\sum_{j=1}^5 a(n-j))$ where $\pi = A000720$.
Note on indices: for $n \ge 0$, $a(n)$ corresponds to $A_{n+1}$ in the OEIS sequence.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | i + 5 =>
    let sumTerms := a (i + 4) + a (i + 3) + a (i + 2) + a (i + 1) + a i
    π sumTerms

/--
A general sequence defined by the Pentanacci $\pi$ recurrence, starting with arbitrary initial
values $v: \text{Fin } 5 \to \mathbb{N}$.
The sequence $a_{\mathrm{general}}(v, n)$ is the n-th term (0-indexed).
-/
noncomputable def aGeneral (v : Fin 5 → ℕ) (n : ℕ) : ℕ :=
  match n with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | i + 5 =>
    let sumTerms :=
      aGeneral v (i + 4) + aGeneral v (i + 3) + aGeneral v (i + 2) + aGeneral v (i + 1) +
        aGeneral v i
    π sumTerms

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by rfl

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ v : Fin 5 → ℕ, (∀ i, 0 < v i) → ∃ c ∈ ({66, 67, 68, 70, 71, 72} : Finset ℕ),
    ∀ᶠ n in Filter.atTop, aGeneral v n = c

end Problem
