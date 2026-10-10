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

- problem_id: CourtadeKumar
- collection: openai-math
- question_id: openai-math:119
- source: openai-math
- source_locator: lean/ComparatorChallenges/CourtadeKumar.lean#OAI.LeanBlast.CourtadeKumar.courtadeKumarAndAttainment
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the Courtade–Kumar conjecture: among Boolean functions of independent uniform bits, a single coordinate retains the most mutual information after independent bit-flip noise. A stronger theorem treats randomized binary summaries at fixed initial information. The Hellinger conjecture is also proved for every Boolean output bias and noise correlation. ([Lean](lean/docs/119.md)) We prove sharp contraction of the information carried by a binary channel under independent symmetric noise on a uniform discrete cube. At fixed initial information, a noisy coordinate retains the most information. The Boolean specialization resolves the Courtade–Kumar conjecture and gives an output-entropy refinement. We also establish a stronger mean-dependent entropy-production bound. The proof combines an explicit three-point optimizer for the local joining problem, two entropy capacities, and a common-output thinning inequality, followed by dimension induction and integration along the noise semigroup.
- notes: OpenAI math result family 119, The Courtade–Kumar and Hellinger conjectures -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/119.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LeanBlast.CourtadeKumar.courtadeKumarAndAttainment
- source_theorem_count: 1
- source_solution_module: OAI.InformationTheory.BooleanNoise.Main
- source_main_result: OAI.LeanBlast.CourtadeKumar.courtadeKumarAndAttainment
- source_papers: preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/main.pdf
- source_scope_note: lean/docs/119.md
- source_field: InformationTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

abbrev Cube (n : ℕ) := Fin n → Bool

end LeanBlast.GotsmanLinial

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

abbrev Cube (n : ℕ) := LeanBlast.GotsmanLinial.Cube n

def cubeAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (∑ x, g x) / (2 : ℝ) ^ n

def ell : ℝ := Real.log 2

def bitFlipKernel {n : ℕ} (ε : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - ε else ε

def jointProbability {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) : ℝ :=
  cubeAverage (fun x => if f x = b then bitFlipKernel ε x y else 0)

def functionMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) : ℝ :=
  ∑ y, jointProbability ε f b y

def observationMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (y : Cube n) : ℝ :=
  ∑ b : Bool, jointProbability ε f b y

def xlogx (t : ℝ) : ℝ := t * Real.log t

def binaryEntropy (ε : ℝ) : ℝ :=
  -(xlogx ε + xlogx (1 - ε)) / ell

def mutualInformation {n : ℕ} (ε : ℝ) (f : Cube n → Bool) : ℝ :=
  (∑ b : Bool, ∑ y : Cube n,
    if 0 < jointProbability ε f b y then
      jointProbability ε f b y *
        Real.log (jointProbability ε f b y /
          (functionMarginal ε f b * observationMarginal ε f y))
    else 0) / ell

def dictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := x i

def complementDictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := !(x i)

def CourtadeKumarStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (1 : ℝ) / 2 →
      ∀ f : Cube n → Bool, mutualInformation ε f ≤ 1 - binaryEntropy ε

def DictatorAttainmentStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (1 : ℝ) / 2 →
      ∀ i : Fin n,
        mutualInformation ε (dictator i) = 1 - binaryEntropy ε ∧
        mutualInformation ε (complementDictator i) = 1 - binaryEntropy ε

def FullStatement : Prop := CourtadeKumarStatement ∧ DictatorAttainmentStatement

def courtadeKumarAndAttainment_statement : Prop :=
  FullStatement

end LeanBlast.CourtadeKumar

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LeanBlast.CourtadeKumar.courtadeKumarAndAttainment_statement

end Problem

/- Formalization scope, from lean/docs/119.md: The formalization proves sharp contraction of the information carried by a binary channel under independent symmetric noise on a uniform discrete cube. At each fixed initial information level, a noisy coordinate channel attains the maximum retained information. It also proves the refined Boolean bound that accounts for output bias, with strict improvement for nonconstant biased outputs at nonzero noise correlation, and the selected mean-dependent entropy-production inequality. For Boolean functions this includes the Courtade–Kumar inequality $I(f(X);Y)\le1-h_2(\varepsilon)$ in bits at crossover probability $0\le\varepsilon\le1/2$, where $h_2$ is binary entropy. A coordinate and its complement attain equality. -/
