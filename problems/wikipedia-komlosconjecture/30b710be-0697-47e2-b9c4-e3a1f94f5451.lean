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

- problem_id: NKomlosConjecture_komlos_conjecture
- collection: wikipedia
- question_id: wikipedia:KomlosConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/KomlosConjecture.lean#komlos_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **The Komlós conjecture** There exists a universal constant $K > 0$ such that for all $n, m \in \mathbb{N}$ and all vectors $v\_1, \dots, v\_n \in \mathbb{R}^m$ with $\|v\_i\|\_2 \le 1$ (encoded here as $\sum\_j v\_{ij}^2 \le 1$), there exist signs $\varepsilon\_i \in \{-1, +1\}$ such that $\left\|\sum\_i \varepsilon\_i v\_i\right\|\_\infty \le K$, i.e. $\left|\sum\_i \varepsilon\_i v\_{ij}\right| \le K$ for every coordinate $j$. Proved by Guo, Fang and Lu with $K = 3\sqrt{2\pi}$ and by Karingula and Lovett with $K = 36$.
- notes: Wikipedia: KomlosConjecture -- https://en.wikipedia.org/wiki/Discrepancy_theory#Major_open_problems
- track: solved
- answer_shape: proof
- source_stem: KomlosConjecture
- source_namespace: KomlosConjecture
- source_theorem: komlos_conjecture
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: komlos_conjecture.variants.zero_vectors
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
Sanity check: with no vectors at all ($n = 0$), the empty signed sum is $0$ in every
coordinate, so any constant bound holds.
-/
@[category test, AMS 5]
theorem komlos_conjecture.variants.zero_vectors (m : ℕ) (v : Fin 0 → Fin m → ℝ) :
    ∃ ε : Fin 0 → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ j, |∑ i, ε i * v i j| ≤ 1 :=
  ⟨Fin.elim0, fun i => i.elim0, by simp⟩

abbrev Target : Prop :=
    ∃ K : ℝ, 0 < K ∧ ∀ (n m : ℕ) (v : Fin n → Fin m → ℝ),
      (∀ i, ∑ j, (v i j) ^ 2 ≤ 1) →
      ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ j, |∑ i, ε i * v i j| ≤ K

end Problem
