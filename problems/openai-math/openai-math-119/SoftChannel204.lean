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

- problem_id: SoftChannel204
- collection: openai-math
- question_id: openai-math:119
- source: openai-math
- source_locator: lean/ComparatorChallenges/SoftChannel204.lean#OAI.SoftChannel204.fullMain
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the Courtade–Kumar conjecture: among Boolean functions of independent uniform bits, a single coordinate retains the most mutual information after independent bit-flip noise. A stronger theorem treats randomized binary summaries at fixed initial information. The Hellinger conjecture is also proved for every Boolean output bias and noise correlation. ([Lean](lean/docs/119.md)) We prove sharp contraction of the information carried by a binary channel under independent symmetric noise on a uniform discrete cube. At fixed initial information, a noisy coordinate retains the most information. The Boolean specialization resolves the Courtade–Kumar conjecture and gives an output-entropy refinement. We also establish a stronger mean-dependent entropy-production bound. The proof combines an explicit three-point optimizer for the local joining problem, two entropy capacities, and a common-output thinning inequality, followed by dimension induction and integration along the noise semigroup.
- notes: OpenAI math result family 119, The Courtade–Kumar and Hellinger conjectures -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/119.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SoftChannel204.fullMain
- source_theorem_count: 1
- source_solution_module: OAI.InformationTheory.SoftChannel.Main
- source_papers: preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/main.pdf
- source_scope_note: lean/docs/119.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators

namespace SoftChannel204

abbrev Cube (n : ℕ) := Fin n → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

def avg {n : ℕ} (g : Cube n → ℝ) : ℝ := (∑ x, g x) / (2 : ℝ) ^ n

def L : ℝ := Real.log 2

def psi (r : ℝ) : ℝ :=
  (1 + r) / 2 * Real.log (1 + r) + (1 - r) / 2 * Real.log (1 - r)

def H (r : ℝ) : ℝ := L - psi r

def info {n : ℕ} (u : Cube n → ℝ) : ℝ := H (avg u) - avg (H ∘ u)

def psiInv (s : ℝ) : ℝ := Function.invFunOn psi (Set.Icc 0 1) s

def kernel {n : ℕ} (ρ : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2

def noise {n : ℕ} (ρ : ℝ) (u : Cube n → ℝ) (y : Cube n) : ℝ :=
  ∑ x, kernel ρ y x * u x

def Closed {n : ℕ} (u : Cube n → ℝ) : Prop := ∀ x, u x ∈ Set.Icc (-1) 1

def Interior {n : ℕ} (g : Cube n → ℝ) : Prop := ∀ x, g x ∈ Set.Ioo (-1) 1

def softCoordinate {n : ℕ} (i : Fin n) (a : ℝ) (x : Cube n) : ℝ := a * sign (x i)

def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n := Function.update x i (!(x i))

def numberOperator {n : ℕ} (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (g x - g (flip i x))

def production {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  avg (fun x => Real.artanh (g x) * numberOperator g x)

/-- Defined by this formula on `[0, L)`; no finite endpoint value at `L` is asserted. -/
def F (s : ℝ) : ℝ := psiInv s * Real.artanh (psiInv s)

/-- The excess `F s - 2 * s`, used for `s < L`, is extended by zero to negative arguments. -/
def S (s : ℝ) : ℝ := if s < 0 then 0 else F s - 2 * s

/-- The reserve is used for `|m| < 1` and `0 ≤ I < H m`. -/
def reserve (m I : ℝ) : ℝ :=
  2 * I + (1 - m ^ 2) * S (L - (H m - I) / (1 - m ^ 2))

def hybrid (m I : ℝ) : ℝ := max (reserve m I) (F I)

def softJoint {n : ℕ} (ρ : ℝ) (u : Cube n → ℝ) (b : Bool) (y : Cube n) : ℝ :=
  avg (fun x => (1 + sign b * u x) / 2 * kernel ρ x y)

def boolJoint {n : ℕ} (ρ : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) : ℝ :=
  avg (fun x => if f x = b then kernel ρ x y else 0)

def leftMarginal {n : ℕ} (p : Bool → Cube n → ℝ) (b : Bool) : ℝ := ∑ y, p b y

def rightMarginal {n : ℕ} (p : Bool → Cube n → ℝ) (y : Cube n) : ℝ := ∑ b, p b y

def mutualInformation {n : ℕ} (p : Bool → Cube n → ℝ) : ℝ :=
  ∑ b, ∑ y, if 0 < p b y then
    p b y * Real.log (p b y / (leftMarginal p b * rightMarginal p y)) else 0

def binaryEntropyBits (ε : ℝ) : ℝ :=
  -(ε * Real.log ε + (1 - ε) * Real.log (1 - ε)) / L

def SoftContraction : Prop := ∀ (n : ℕ) (u : Cube n → ℝ), Closed u →
  ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
    info (noise ρ u) ≤ psi (|ρ| * psiInv (info u))

def SoftAttainment : Prop := ∀ (n : ℕ) (i : Fin n) (a : ℝ), |a| ≤ 1 →
  ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
    info (noise ρ (softCoordinate i a)) =
      psi (|ρ| * psiInv (info (softCoordinate i a)))

def SoftInformationIdentity : Prop := ∀ (n : ℕ) (u : Cube n → ℝ), Closed u →
  ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
    mutualInformation (softJoint ρ u) = info (noise ρ u)

def RefinedBoolean : Prop := ∀ (n : ℕ) (f : Cube n → Bool)
  (ρ : ℝ), ρ ∈ Set.Icc (-1 : ℝ) 1 →
  let m := avg (sign ∘ f)
  let bound := psi (|ρ| * psiInv (H m))
  mutualInformation (boolJoint ρ f) = info (noise ρ (sign ∘ f)) ∧
  mutualInformation (boolJoint ρ f) ≤ bound ∧ bound ≤ psi |ρ| ∧
  (0 < |m| → |m| < 1 → 0 < |ρ| → bound < psi |ρ|)

def BooleanAttainment : Prop := ∀ (n : ℕ) (i : Fin n)
  (ρ : ℝ), ρ ∈ Set.Icc (-1 : ℝ) 1 →
  mutualInformation (boolJoint ρ (fun x => x i)) = psi |ρ| ∧
  mutualInformation (boolJoint ρ (fun x => !(x i))) = psi |ρ|

def BitsConversion : Prop := ∀ (n : ℕ) (f : Cube n → Bool)
  (ε : ℝ), ε ∈ Set.Icc (0 : ℝ) (1/2) →
  psi (1 - 2 * ε) / L = 1 - binaryEntropyBits ε ∧
  mutualInformation (boolJoint (1 - 2 * ε) f) / L ≤ 1 - binaryEntropyBits ε

def SharpProduction : Prop := ∀ (n : ℕ) (g : Cube n → ℝ), Interior g →
  hybrid (avg g) (info g) ≤ production g ∧ F (info g) ≤ hybrid (avg g) (info g)

def FullMain : Prop := SoftContraction ∧ SoftAttainment ∧ SoftInformationIdentity ∧
  RefinedBoolean ∧ BooleanAttainment ∧ BitsConversion ∧ SharpProduction

def fullMain_statement : Prop :=
  FullMain

end SoftChannel204

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SoftChannel204.fullMain_statement

end Problem

/- Formalization scope, from lean/docs/119.md: The formalization proves sharp contraction of the information carried by a binary channel under independent symmetric noise on a uniform discrete cube. At each fixed initial information level, a noisy coordinate channel attains the maximum retained information. It also proves the refined Boolean bound that accounts for output bias, with strict improvement for nonconstant biased outputs at nonzero noise correlation, and the selected mean-dependent entropy-production inequality. For Boolean functions this includes the Courtade–Kumar inequality $I(f(X);Y)\le1-h_2(\varepsilon)$ in bits at crossover probability $0\le\varepsilon\le1/2$, where $h_2$ is binary entropy. A coordinate and its complement attain equality. -/
