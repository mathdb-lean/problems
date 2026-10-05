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

- problem_id: BBugeaudDistributionModuloOne_Problem10_4_spectrum_xi_alpha_pow_countable
- collection: books
- question_id: books:BugeaudDistributionModuloOne/Problem10_4
- source: formal-conjectures
- source_locator: FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_4.lean#spectrum_xi_alpha_pow_countable
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Problem 10.4. Let $\xi$ be a non-zero real number and $\alpha > 1$ be a real number. Is the spectrum of the sequence $(\xi \alpha^n)_{n \ge 1}$ at most countable? Posed by Mendès France [Men73]. The answer is no. Özcan [Özc26] disproved this for every $\alpha > 1$; the counterexample formalised here takes $\alpha = 64$ and the real number $\xi = $ `xiVal`, whose spectrum contains the uncountable set of irrational numbers of the form `thetaSeq u`.
- notes: Book problem BugeaudDistributionModuloOne/Problem10_4 -- https://arxiv.org/abs/2609.07714
- track: solved
- answer_shape: decide
- source_stem: BugeaudDistributionModuloOne/Problem10_4
- source_namespace: Bugeaud04
- source_theorem: spectrum_xi_alpha_pow_countable
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

/--
The spectrum of a sequence $(x_n)_{n \ge 1}$ of real numbers is the set of
irrational real numbers $\theta \in (0, 1)$ such that the sequence
$(x_n - n\theta)_{n \ge 1}$ is not uniformly distributed modulo one.
-/
def Spectrum (x : ℕ → ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Ioo (0 : ℝ) 1 ∧ Irrational θ ∧
    ¬ IsEquidistributedModuloOne (fun n => x n - n * θ)}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (ξ : ℝ), ξ ≠ 0 → ∀ (α : ℝ), 1 < α → (Spectrum (fun n => ξ * α ^ n)).Countable

end Problem
