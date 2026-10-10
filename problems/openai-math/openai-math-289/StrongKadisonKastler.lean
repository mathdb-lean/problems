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

- problem_id: StrongKadisonKastler
- collection: openai-math
- question_id: openai-math:289
- source: openai-math
- source_locator: lean/ComparatorChallenges/StrongKadisonKastler.lean#OAI.KadisonKastler.universal_strong_stability
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that sufficiently close unital von Neumann algebras on the same Hilbert space are conjugate by a unitary arbitrarily close to the identity, with a universal tolerance in the operator-norm distance between unit balls. Counterexamples show that near-identity conjugacy fails for one-sided near inclusions, and that arbitrarily close norm-separable C∗-algebras need not be ambiently unitarily conjugate. ([Lean](lean/docs/289.md)) We prove that sufficiently close unital von Neumann algebras are conjugate by a unitary arbitrarily close to the identity. The tolerance depends only on the prescribed distance of that unitary from the identity, uniformly over all algebras, representations, and Hilbert spaces. This resolves the strong Kadison–Kastler conjecture.
- notes: OpenAI math result family 289, Strong Kadison–Kastler stability and its spatial boundaries -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/289.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.KadisonKastler.universal_strong_stability
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.KadisonKastler.StrongStability
- source_papers: preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf
- source_scope_note: lean/docs/289.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Theorem 1.1 of *Universal strong Kadison–Kastler stability*:
one tolerance gives small unitary conjugacies on every complex Hilbert space. -/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitBall (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {x | x ∈ M ∧ ‖x‖ ≤ 1}

noncomputable def kkDistance (M N : VonNeumannAlgebra H) : ℝ :=
  Metric.hausdorffDist (unitBall M) (unitBall N)

def unitaryConj (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) : H →L[ℂ] H :=
  (v : H →L[ℂ] H) * x * star (v : H →L[ℂ] H)

def Conjugates (v : unitary (H →L[ℂ] H)) (M N : VonNeumannAlgebra H) : Prop :=
  unitaryConj v '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H))

def NearConjugacy (M N : VonNeumannAlgebra H) (ε : ℝ) : Prop :=
  ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧ ‖(v : H →L[ℂ] H) - 1‖ < ε

def UniversalStrongStability : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ∀ M N : VonNeumannAlgebra H,
        kkDistance M N < δ → NearConjugacy M N ε

def universal_strong_stability_statement : Prop :=
  UniversalStrongStability.{u}

end

end KadisonKastler

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.KadisonKastler.universal_strong_stability_statement.{u}

end Problem

/- Formalization scope, from lean/docs/289.md: The formalization proves the strong Kadison–Kastler conjecture uniformly. For every $\varepsilon>0$, there is a $\delta>0$ such that any two unital von Neumann algebras on the same complex Hilbert space at Kadison–Kastler distance below $\delta$ are conjugate by a unitary $u$ with $\lVert u-1\rVert<\varepsilon$. The tolerance depends only on $\varepsilon$, uniformly over the algebras, their representations, and the Hilbert space. -/
