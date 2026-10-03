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

- problem_id: E116
- collection: erdos
- question_id: erdos:116
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/116.lean#erdos_116
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $p(z)=\prod_{i=1}^n (z-z_i)$ for $\lvert z_i\rvert \leq 1$. Is it true that $$\lvert\{ z: \lvert p(z)\rvert <1\}\rvert>n^{-O(1)}$$ (or perhaps even $>(\log n)^{-O(1)}$)? Conjectured by Erdős, Herzog, and Piranian [EHP58]. The lower bound $\gg n^{-4}$ follows from a result of Pommerenke [Po61]. The lower bound $\gg (\log n)^{-1}$ was proved by Krishnapur, Lundberg, and Ramachandran [KLR25]. Wagner [Wa88] proves, for $n\geq 3$, the existence of such polynomials with $$\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \ll_\epsilon (\log\log n)^{-1/2+\epsilon}$$ for all $\epsilon>0$. Krishnapur, Lundberg, and Ramachandran [KLR25] improved this upper bound to $\ll (\log\log n)^{-1}$. Pólya [Po28] showed the upper bound $\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \leq \pi$ always holds, and this is achieved only when the $z_i$ are identical.
- notes: Erdos Problem 116 -- https://www.erdosproblems.com/116
- track: solved
- answer_shape: decide
- source_stem: 116
- mathdb_ref: erdos:116
- source_namespace: Erdos116
- source_theorem: erdos_116
- source_category: research solved
- source_ams: 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open MeasureTheory

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, ∀ n : ℕ, 0 < n →
        ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) →
          ENNReal.ofReal (c / n ^ C) ≤ volume {w : ℂ | ‖∏ i, (w - z i)‖ < 1}

end Problem
