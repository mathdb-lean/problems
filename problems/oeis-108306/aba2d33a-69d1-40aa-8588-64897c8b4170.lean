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

- problem_id: O108306_conjecture
- collection: oeis
- question_id: oeis:108306
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/108306.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The conjecture: The INVERT transform of a sequence starting $(1, a, ab, ab^2, ab^3, \ldots)$ is equivalent to extracting the upper left terms of powers of the 2x2 matrix [(1,a); (1,b)].
- notes: OEIS A108306 -- https://oeis.org/A108306
- track: solved
- answer_shape: proof
- source_stem: 108306
- source_namespace: OeisA108306
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_is_invert_transform_case
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The primary defining sequence `a`.
`a n` is the $n$-th term of the expansion of $(3x+1)/(1-3x-3x^2)$,
satisfying $a(0)=1, a(1)=6, a(n)=3a(n-1)+3a(n-2)$. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | k + 2 => 3 * a (k + 1) + 3 * a k

open Matrix

/--
The matrix for the specific case $a=5, b=2$.
$$M = \begin{pmatrix} 1 & 5 \cr 1 & 2 \end{pmatrix}$$
-/
def m : Matrix (Fin 2) (Fin 2) ℕ :=
  fun i j => match i, j with
  | 0, 0 => 1
  | 0, 1 => 5
  | 1, 0 => 1
  | 1, 1 => 2

/--
The c sequence for the general INVERT transform conjecture.
$c(1) = 1$, $c(k)=ab^(k-2)$ for $k \ge 2$.
-/
def invertSeqC (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (k + 2) => a * b^k

/-- The INVERT transform of the sequence c. -/
noncomputable def invertSeqD (a b : ℕ) (n : ℕ) : ℕ :=
  Nat.strongRecOn n
    (fun m ih =>
      if m = 0 then 1
      else ∑ i ∈ Finset.range m,
        if h : i < m then invertSeqC a b (m - i) * ih i h else 0)

/-- The general 2x2 matrix [(1,a); (1,b)]. -/
def genMatrix (a b : ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  fun i j => match i, j with
  | 0, 0 => 1
  | 0, 1 => a
  | 1, 0 => 1
  | 1, 1 => b

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 6 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 21 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 81 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 306 := by decide

/--
The sequence is the INVERT transform of (1, 5, 10, 20, 40, 80, 160, ...) and can be obtained
by extracting the upper left terms of matrix powers of [(1,5); (1,2)].
These results are a case (a=5, b=2) of the general conjecture below.
-/
@[category textbook, AMS 11]
theorem a_is_invert_transform_case (n : ℕ) :
    a n = (m ^ (n + 1)) 0 0 := by
  -- `m` satisfies `m ^ 2 = 3 m + 3`, so its powers satisfy the recurrence of `a`.
  have hm : ∀ n, m ^ (n + 2) = 3 • m ^ (n + 1) + 3 • m ^ n := fun n => by
    rw [pow_add, show m ^ 2 = 3 • m + 3 • (1 : Matrix (Fin 2) (Fin 2) ℕ) by decide, mul_add,
      mul_smul_comm, mul_smul_comm, mul_one, ← pow_succ]
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih1 ih2 =>
    rw [a, ih1, ih2, show k + 2 + 1 = k + 1 + 2 by omega, hm (k + 1)]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

abbrev Target : Prop :=
    ∀ (a_val b_val n : ℕ),
      invertSeqD a_val b_val n = (genMatrix a_val b_val ^ n) 0 0

end Problem
