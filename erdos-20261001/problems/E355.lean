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

- problem_id: E355
- collection: erdos
- question_id: erdos:355
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/355.lean#erdos_355
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a lacunary sequence $A\subseteq \mathbb{N}$ (so that $A=\{a_1 < \cdots\}$ and there exists some $\lambda > 1$ such that $a_{n+1}/a_n\geq \lambda$ for all $n\geq 1$) such that $$\left\{ \sum_{a\in A'}\frac{1}{a} : A'\subseteq A\textrm{ finite}\right\}$$ contain all rationals in some open interval? Bleicher and Erdős conjectured the answer is no. In fact the answer is yes, with any lacunarity constant $\lambda\in (1,2)$ (though not $\lambda=2$), as proved by van Doorn and Kova\v{c} [DoKo25]. This was formalized in Lean by van Doorn using Aristotle.
- notes: Erdos Problem 355 -- https://www.erdosproblems.com/355
- track: solved
- answer_shape: decide
- source_stem: 355
- mathdb_ref: erdos:355
- source_namespace: Erdos355
- source_theorem: erdos_355
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ A : ℕ → ℕ, IsLacunary A ∧ ∃ u v : ℝ, u < v ∧ ∀ q : ℚ, ↑q ∈ Set.Ioo u v →
      q ∈ {∑ a ∈ A', (1 / a : ℚ) | (A' : Finset ℕ) (_ : ↑A' ⊆ Set.range A)}

end Problem
