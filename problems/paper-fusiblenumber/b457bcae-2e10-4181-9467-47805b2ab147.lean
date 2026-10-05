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

- problem_id: RFusibleNumber_conj_7_1
- collection: paper
- question_id: paper:FusibleNumber
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/FusibleNumber.lean#conj_7_1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If `x` is a fusible number and `y` is its successor, then the interval `[x + 1, y + 1)` can be divided into intervals `[ℓₙ, ℓₙ₊₁)`, such that the fusible numbers in `[ℓₙ, ℓₙ₊₁)` are obtained by fusing the `n + 1`st successor of `x` with a fusible number. This formalization differs from Conjecture 7.1 in the paper in four ways: (1) it is obtained from Conjecture 7.1 by plugging in `n + 1` into `n`, which simplifies the expressions and removes the need to assume `n ≥ 1`; (2) the `n + 1`st successor `s^(n+1)(x)` is replaced by the explicit value `x + (2 - 1 / 2 ^ n) * m`; (3) instead of defining `y` to be the successor of `x`, we assert that there is no fusible number strictly between `x` and `y`; (4) instead of using `∃ z, IsFusible z ∧ q = s^(n+1)(x) ~ z` we use the value of `z` determined by the equality, namely `z = 2 * q - 1 - s^(n+1)(x)`, and it is easy to see `z ∈ [x + 1 - m / 2 ^ n, x + 1)` as required.
- notes: Problem from FusibleNumber -- https://arxiv.org/abs/2003.14342
- track: open
- answer_shape: proof
- source_stem: FusibleNumber
- source_namespace: FusibleNumber
- source_theorem: conj_7_1
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: isFusible_one_half isFusible_one
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
A rational number is fusible if it belongs to the smallest set containing $0$ and closed under
the operation
$$
a \sim b = \frac{a + b + 1}{2}
$$
whenever $|a-b| < 1$.
-/
inductive IsFusible : ℚ → Prop
  | zero : IsFusible 0
  | fuse (a b : ℚ) : IsFusible a → IsFusible b → |a - b| < 1 → IsFusible ((a + b + 1) / 2)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The rational number $1/2$ is fusible. -/
@[category test, AMS 5]
theorem isFusible_one_half : IsFusible (1 / 2 : ℚ) := by
  have h := IsFusible.fuse 0 0 IsFusible.zero IsFusible.zero (by norm_num)
  norm_num at h
  exact h

/-- The rational number $1$ is fusible. -/
@[category test, AMS 5]
theorem isFusible_one : IsFusible (1 : ℚ) := by
  have h := IsFusible.fuse (1 / 2) (1 / 2) isFusible_one_half isFusible_one_half (by norm_num)
  norm_num at h
  exact h

abbrev Target : Prop :=
    ∀ (x y q : ℚ) (n : ℕ) (fus_x : IsFusible x) (fus_y : IsFusible y) (lt : x < y)
        (nmem_Ioo : ∀ z, IsFusible z → z ∉ Set.Ioo x y),
      let m := y - x
      let ℓ (n : ℕ) := y + 1 - m / 2 ^ n
      IsFusible q → q ∈ Set.Ico (ℓ n) (ℓ (n + 1)) → IsFusible (2 * q - 1 - x - (2 - 1 / 2 ^ n) * m)

end Problem
