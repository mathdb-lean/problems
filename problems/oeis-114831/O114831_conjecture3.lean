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

- problem_id: O114831_conjecture3
- collection: oeis
- question_id: oeis:114831
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/114831.lean#conjecture3
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture based on OEIS A114831: What is this sequence, asymptotically? If the limit exists, the ratio of consecutive terms must tend to $\sqrt{3}$: $$ \lim_{n \to \infty} \frac{a(n+1)}{a(n)} = \sqrt{3}. $$ That's because $a(n)$ is positive, monotonically increasing ($a(n) > a(n-1)$) and $a(n+2) \geq a(n+1) + a(n)$. So $a(n)$ grows exponentially, at least as fast as the Fibonnaci numbers. Assuming $\frac{a(n+1)}{a(n)}$ tend to a limit L, solving for L in the definition of $a(n)$ gives $L=\sqrt{3}$.
- notes: OEIS A114831 -- https://oeis.org/A114831
- track: solved
- answer_shape: proof
- source_stem: 114831
- source_namespace: OeisA114831
- source_theorem: conjecture3
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter Real Topology

/--
The primary defining sequence `a`.
Each term is previous term plus floor of harmonic mean of two previous terms.
-/
noncomputable def a : ℕ → ℕ
| 0 => 0 -- Dummy value, sequence starts at index 1
| 1 => 1
| 2 => 2
| n + 3 =>
  let an1 : ℕ := a (n + 2)
  let an2 : ℕ := a (n + 1)
  let num : ℚ := (2 * an1 * an2 : ℕ).cast
  let den : ℚ := (an1 + an2 : ℕ).cast
  let harmonicTermFloor : ℕ := Int.toNat (num / den).floor
  an1 + harmonicTermFloor

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by norm_num [a]

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by rw [a]

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  norm_num [a, Rat.floor, Int.toNat]

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  norm_num [a, Rat.floor, Int.toNat]

abbrev Target : Prop :=
    Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ)) atTop (nhds (Real.sqrt 3))

end Problem
