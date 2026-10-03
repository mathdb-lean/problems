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

- problem_id: E1005
- collection: erdos
- question_id: erdos:1005
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1005.lean#erdos_1005
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\frac{a_1}{b_1}, \frac{a_2}{b_2}, \ldots$ be the Farey fractions of order $n \geq 4$. Let $f(n)$ be the largest integer such that if $1 \leq k < l \leq k + f(n)$ then $\frac{a_k}{b_k}$ and $\frac{a_l}{b_l}$ are similarly ordered, in other words $(a_k - a_l)(b_k - b_l) \geq 0$. Estimate $f(n)$: in particular, is there a constant $c > 0$ such that $f(n) = (c + o(1)) n$ for all large $n$? Mayer [Ma42] proved that $f(n) \to \infty$ and Erdős [Er43] that $f(n) \gg n$. Van Doorn [vD25b] proved $(1/12 - o(1)) n \le f(n) \le n / 4 + O(1)$ and conjectured that $f(n) = (1/4 + o(1)) n$, which was proved by Cipollini and GPT-5.5; see `erdos_1005.variants.constant`.
- notes: Erdos Problem 1005 -- https://www.erdosproblems.com/1005
- track: solved
- answer_shape: decide
- source_stem: 1005
- mathdb_ref: erdos:1005
- source_namespace: Erdos1005
- source_theorem: erdos_1005
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter
open scoped Topology

namespace Problem

/-- A rational `q` is a Farey fraction of order `n` if it lies in `[0, 1]` and has denominator at
most `n`. (Every `q : ℚ` is stored in lowest terms, so `q.den` and `q.num` are the reduced
denominator and numerator.) -/
def IsFarey (n : ℕ) (q : ℚ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ q.den ≤ n

/-- The number of Farey fractions of order `n` strictly between `x` and `y`. -/
noncomputable def betweenCount (n : ℕ) (x y : ℚ) : ℕ :=
  {q : ℚ | IsFarey n q ∧ x < q ∧ q < y}.ncard

/-- `f n` is the largest integer such that any two Farey fractions of order `n` whose indices
differ by at most `f n` are similarly ordered: it is the minimum, over all pairs `x < y` of Farey
fractions of order `n` with `(x.num - y.num) * (x.den - y.den) < 0`, of the number of Farey
fractions strictly between `x` and `y`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k | ∃ x y : ℚ, IsFarey n x ∧ IsFarey n y ∧ x < y ∧
    (x.num - y.num) * ((x.den : ℤ) - y.den) < 0 ∧ betweenCount n x y = k}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 c)

end Problem
