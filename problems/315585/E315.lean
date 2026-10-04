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

- problem_id: E315
- collection: erdos
- question_id: erdos:315
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/315.lean#erdos_315
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $u_1=1$ and $u_{n+1}=u_n(u_n+1)$, so that $\sum_{k\geq 1}\frac{1}{u_k+1}$ and $u_k=\lfloor c_0^{2^k}+1\rfloor$ for $k\geq 1$, where $$c_0=\lim u_n^{1/2^n}=1.264085\cdots.$$ Let $a_1<a_2<\cdots $ be any other sequence with $\sum \frac{1}{a_k}=1$. Is it true that $$\liminf a_n^{1/2^n}<c_0=1.264085\cdots?$$ This is true, and was proved independently by Kamio [Ka25] and Li and Tang [LiTa25]. An earlier interpretation of this question on this site defined $u_1=2$ and $u_{n+1}=u_n^2-u_n+1$ (Sylvester's sequence), which is the same sequence shifted by $1$; we use the phrasing above as more faithful to [ErGr80]. The constant $c_0$ is called the Vardi constant.
- notes: Erdos Problem 315 -- https://www.erdosproblems.com/315
- track: solved
- answer_shape: decide
- source_stem: 315
- mathdb_ref: erdos:315
- source_namespace: Erdos315
- source_theorem: erdos_315
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

/-- The sequence $u_1=1$, $u_{n+1}=u_n(u_n+1)$, indexed here so that `u i` is $u_{i+1}$:
`u 0 = 1`, `u 1 = 2`, `u 2 = 6`, `u 3 = 42`, … (so `u i + 1` is Sylvester's sequence
$2, 3, 7, 43, \ldots$). -/
def u : ℕ → ℕ
  | 0 => 1
  | n + 1 => u n * (u n + 1)

/-- The Vardi constant $c_0=\lim u_n^{1/2^n}=1.264085\cdots$. With the `0`-indexing of `u`, the
$n$-th term $u_n^{1/2^n}$ of the defining sequence is `(u i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))` at
`i = n - 1`. -/
noncomputable def c₀ : ℝ := limUnder atTop fun i => (u i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ a : ℕ → ℕ, (∀ i, 0 < a i) → StrictMono a → (∃ i, a i ≠ u i + 1) →
          ∑' i, (1 : ℝ) / a i = 1 →
          atTop.liminf (fun i => (a i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))) < c₀

end Problem
