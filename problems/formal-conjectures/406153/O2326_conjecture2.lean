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

- problem_id: O2326_conjecture2
- collection: oeis
- question_id: oeis:2326
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/2326.lean#conjecture2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: A generalization of the previous conjecture: For each $k \ge 2$, if $p$ is an odd prime then $a((p^{k+1}-1)/2) = p \cdot a((p^k-1)/2)$. Computer testing of this generalized conjecture shows that there is no counterexample for $k$ and $p$ both up to 1000. - [Ahmad J. Masad](https://oeis.org/wiki/User:Ahmad_J._Masad), Oct 17 2020 The two are in fact equivalent. Its $k = 2$ instance is `conjecture1`. Conversely, write $d = \operatorname{ord}_{p^2}(2)$. `conjecture1` for $p$ says $v_p(2^d - 1) = 2$, and lifting the exponent for the odd prime $p$ then gives $v_p(2^{d p^t} - 1) = 2 + t$, hence $\operatorname{ord}_{p^{2+t}}(2) = d p^t$ for every $t \ge 0$, which is every instance for that $p$.
- notes: OEIS A2326 -- https://oeis.org/A2326
- track: open
- answer_shape: proof
- source_stem: 2326
- source_namespace: OeisA2326
- source_theorem: conjecture2
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The multiplicative order of 2 modulo $2n+1$. -/
noncomputable def a (n : ℕ) : ℕ :=
  orderOf (2 : ZMod (2 * n + 1))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  dsimp [a]
  exact Subsingleton.orderOf_eq (2 : ZMod 1)

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  dsimp [a]
  rw [orderOf_eq_iff (by decide)]
  exact ⟨by decide, fun m hm1 hm2 ↦ by interval_cases m; decide⟩

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by
  dsimp [a]
  rw [orderOf_eq_iff (by decide)]
  exact ⟨by decide, fun m hm1 hm2 ↦ by interval_cases m <;> decide⟩

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  dsimp [a]
  rw [orderOf_eq_iff (by decide)]
  exact ⟨by decide, fun m hm1 hm2 ↦ by interval_cases m <;> decide⟩

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by
  dsimp [a]
  rw [orderOf_eq_iff (by decide)]
  exact ⟨by decide, fun m hm1 hm2 ↦ by interval_cases m <;> decide⟩

abbrev Target : Prop :=
    ∀ (k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2),
      a ((p ^ (k + 1) - 1) / 2) = p * a ((p ^ k - 1) / 2)

end Problem
