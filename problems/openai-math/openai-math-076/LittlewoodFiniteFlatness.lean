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

- problem_id: LittlewoodFiniteFlatness
- collection: openai-math
- question_id: openai-math:076
- source: openai-math
- source_locator: lean/ComparatorChallenges/LittlewoodFiniteFlatness.lean#OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs polynomials with N consecutive coefficients in $`\{-1,1\}`$ whose modulus is $`(1+o(1))\sqrt N`$ uniformly on the entire unit circle, for every sufficiently large integer length N. Thus real Littlewood polynomials are ultraflat, including at the real endpoints. Their binary merit factors tend to infinity, disproving Turyn's bounded-merit-factor conjecture. ([Lean](lean/docs/076.md)) We prove that the minimum possible maximum modulus on the unit circle of a polynomial with N consecutive real coefficients in $`\{-1,1\}`$ is $`(1+o(1))\sqrt N`$, as N tends to infinity through all integers. This disproves the real-sign analogue of Erdős's fixed relative-gap conjecture. As a consequence, the largest binary merit factor at length N tends to infinity through all integer lengths, disproving Turyn's conjecture.
- notes: OpenAI math result family 076, Real ultraflat Littlewood polynomials and unbounded binary merit factors -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/076.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Littlewood.FiniteFlatness
- source_papers: preprints/Asymptotically-minimal-maxima-of-real-Littlewood-polynomials-September-23-2026/paper.pdf
- source_scope_note: lean/docs/076.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate

namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

/-- The consecutive-degree polynomial of a real coefficient family. -/
def littlewoodValue {N : ℕ} (ε : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)

/-- Every coefficient is a real sign. -/
def IsRealSigning {N : ℕ} (ε : Fin N → ℝ) : Prop :=
  ∀ k, ε k = -1 ∨ ε k = 1

def MainStatement : Prop :=
  ∃ ε : (N : ℕ) → Fin N → ℝ,
    (∀ N : ℕ, IsRealSigning (ε N)) ∧
    ∀ p : ℝ, 0 < p →
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ t : UnitAddCircle,
            Real.rpow
              |‖littlewoodValue (ε N) (fourier (1 : ℤ) t)‖ /
                  Real.sqrt (N : ℝ) - 1|
              p
            ∂AddCircle.haarAddCircle)
        Filter.atTop (𝓝 (0 : ℝ))

/-- One all-length real-sign family for every finite positive real exponent. -/
def main_statement : Prop :=
  MainStatement

end AsymptoticallyMinimalLittlewoodFiniteFlatness

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.main_statement

end Problem

/- Formalization scope, from lean/docs/076.md: The formalization gives real Littlewood polynomials of every sufficiently large length whose maximum modulus on the unit circle is at most $(1+\eta)\sqrt N$ for any fixed $\eta>0$. Thus the smallest possible maximum is asymptotically minimal through all integer lengths. A further statement chooses one family of real sign polynomials for all lengths such that, for every fixed finite $p>0$, the $L^p$ mean of $\bigl||P_N(z)|/\sqrt N-1\bigr|$ on the unit circle tends to zero. The results are existential and do not give an effective convergence rate or a signing algorithm. -/
