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

- problem_id: E781_parts_ii
- collection: erdos
- question_id: erdos:781
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/781.lean#erdos_781.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that $f(k)=k^2-k+1$ for all $k$? The answer is no, since $f(k)\gg k^3$ by Alon and Spencer [AlSp89].
- notes: Erdos Problem 781 -- https://www.erdosproblems.com/781
- track: solved
- answer_shape: decide
- source_stem: 781
- mathdb_ref: erdos:781
- source_namespace: Erdos781
- source_theorem: erdos_781.parts.ii
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Asymptotics

namespace Problem

/-- A $k$-term *descending wave* is a sequence $x_1<\cdots <x_k$ such that, for $1<j<k$,
$x_j \geq \frac{x_{j+1}+x_{j-1}}{2}$. -/
def IsDescendingWave {k : ℕ} (x : Fin k → ℕ) : Prop :=
  StrictMono x ∧
    ∀ i j l : Fin k, (i : ℕ) + 1 = j → (j : ℕ) + 1 = l → x i + x l ≤ 2 * x j

/-- `f k` is the minimal `n` such that any $2$-colouring of $\{1,\ldots,n\}$ (identified with
`Fin n`) contains a monochromatic $k$-term descending wave. -/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {n | ∀ c : Fin n → Fin 2, ∃ x : Fin k → Fin n,
    IsDescendingWave (fun i ↦ (x i : ℕ)) ∧ ∃ γ, ∀ i, c (x i) = γ}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ k ≥ 1, f k = k ^ 2 - k + 1

end Problem
