import Mathlib
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

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

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: UniformSparsestCut
- collection: openai-math
- question_id: openai-math:117
- source: openai-math
- source_locator: lean/ComparatorChallenges/UniformSparsestCut.lean#OAI.UniformSparsestCut.mainGap
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that approximating Uniform Sparsest Cut within any fixed constant factor is NP-hard, even with nonnegative rational capacities and unit demands. The Goemans–Linial semidefinite relaxation also has integrality gaps of order at least $`\sqrt{\log n}/(\log\log n)^3`$, approaching the square-root-logarithmic upper bound. ([Lean](lean/docs/117.md)) We construct uniform sparsest-cut instances whose Goemans–Linial semidefinite integrality gap is at least $`c\sqrt{\log n}/(\log\log n)^3`$ along a sequence $`n\to\infty`$. The demand is one between every pair of distinct vertices, and the capacities are nonnegative real numbers. This matches the Arora–Rao–Vazirani upper bound up to a power of $`\log\log n`$.
- notes: OpenAI math result family 117, Uniform sparsest cut: hardness and semidefinite gaps -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/117.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.UniformSparsestCut.mainGap
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.SparsestCut.Main
- source_main_result: OAI.UniformSparsestCut.mainGap
- source_papers: preprints/Near-square-root-logarithmic-integrality-gaps-for-uniform-sparsest-cut-September-24-2026/Near-square-root-logarithmic-integrality-gaps-for-uniform-sparsest-cut-September-24-2026.pdf
- source_scope_note: lean/docs/117.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators

namespace UniformSparsestCut

structure Capacity (n : ℕ) where
  cap : Fin n → Fin n → ℝ
  nonneg : ∀ i j, 0 ≤ cap i j
  symm : ∀ i j, cap i j = cap j i
  diagonal : ∀ i, cap i i = 0

def pairSum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then f i j else 0

noncomputable def cutRatio {n : ℕ} (C : Capacity n) (B : Finset (Fin n)) : ℝ :=
  (∑ i ∈ B, ∑ j ∈ Bᶜ, C.cap i j) /
    ((B.card : ℝ) * ((n : ℝ) - (B.card : ℝ)))

noncomputable def OPT {n : ℕ} (C : Capacity n) : ℝ :=
  sInf {r | ∃ B : Finset (Fin n), B.Nonempty ∧ B ≠ Finset.univ ∧ r = cutRatio C B}

def NegativeType {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop :=
  (∃ x : Fin n → EuclideanSpace ℝ (Fin n), ∀ i j, d i j = ‖x i - x j‖ ^ 2) ∧
  ∀ i j k, d i k ≤ d i j + d j k

def Feasible {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop :=
  NegativeType d ∧ pairSum d = 1

noncomputable def glValue {n : ℕ} (C : Capacity n) : ℝ :=
  sInf {r | ∃ d : Fin n → Fin n → ℝ, Feasible d ∧
    r = pairSum (fun i j => C.cap i j * d i j)}

open Filter

def mainGap_statement : Prop :=
  ∃ c : ℝ, 0 < c ∧
      ∃ n : ℕ → ℕ, ∃ C : (j : ℕ) → Capacity (n j),
        (∀ j, 2 ≤ n j) ∧
        Tendsto n atTop atTop ∧
        (∀ j, 0 < glValue (C j)) ∧
        ∀ᶠ j in atTop,
          c * Real.sqrt (Real.log (n j : ℝ)) / (Real.log (Real.log (n j : ℝ))) ^ 3 ≤
            OPT (C j) / glValue (C j)

end UniformSparsestCut

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.UniformSparsestCut.mainGap_statement

end Problem

/- Formalization scope, from lean/docs/117.md: The formalized result gives integrality gaps for the Goemans–Linial relaxation of uniform sparsest cut. Along a sequence of instance sizes $n\to\infty$, the ratio of the integral optimum to the positive relaxation optimum is at least $c\sqrt{\log n}/(\log\log n)^3$ for one absolute $c>0$. Every unordered pair has unit demand, and the relaxation uses squared Euclidean distances satisfying the triangle inequalities. The result is an existential sequence, not a bound for every size or a computational hardness theorem. -/
