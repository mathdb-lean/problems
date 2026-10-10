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

- problem_id: Cotype
- collection: openai-math
- question_id: openai-math:326
- source: openai-math
- source_locator: lean/ComparatorChallenges/Cotype.lean#OAI.Cotype.mainTarget_proved
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the cotype–cotype conjecture for real Banach spaces with the approximation property. Such a nonzero space is K-convex if and only if both it and its dual have finite Rademacher cotype, with possibly different exponents. Equivalently, these cotype assumptions force nontrivial Rademacher type. ([Lean](lean/docs/326.md)) We prove the cotype–cotype conjecture under the ordinary approximation property. A nonzero real Banach space with this property is K-convex if and only if both the space and its dual have finite Rademacher cotype, possibly with different exponents.
- notes: OpenAI math result family 326, The cotype–cotype conjecture under the approximation property -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/326.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Cotype.mainTarget_proved
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Cotype.Main
- source_main_result: OAI.Cotype.mainTarget_proved
- source_papers: preprints/The-cotype-cotype-conjecture-under-the-approximation-property-September-23-2026/paper.pdf
- source_scope_note: lean/docs/326.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators
universe u v

namespace Cotype

abbrev Cube (n : ℕ) := Fin n → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

def average {ι : Type u} [Fintype ι] {E : Type v} [AddCommMonoid E] [Module ℝ E]
    (f : ι → E) : E := (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def cubeL2 {n : ℕ} (f : Cube n → E) : ℝ :=
  Real.sqrt (average (fun ε => ‖f ε‖ ^ 2))

def rademacherSum {n : ℕ} (x : Fin n → E) (ε : Cube n) : E :=
  ∑ i, sign (ε i) • x i

def moment {n : ℕ} (f : Cube n → E) (i : Fin n) : E :=
  average (fun ε => sign (ε i) • f ε)

def radProjection {n : ℕ} (f : Cube n → E) : Cube n → E :=
  rademacherSum E (moment E f)

def KConvex : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (f : Cube n → E),
  cubeL2 E (radProjection E f) ≤ K * cubeL2 E f

def HasCotype (q : ℝ) : Prop := 2 ≤ q ∧ ∃ C : ℝ, 0 ≤ C ∧
  ∀ (n : ℕ) (x : Fin n → E),
    (∑ i, ‖x i‖ ^ q) ^ (1 / q) ≤ C * cubeL2 E (rademacherSum E x)

def FiniteCotype : Prop := ∃ q : ℝ, HasCotype E q

def ApproximationProperty : Prop := ∀ (M : Set E), IsCompact M →
  ∀ δ : ℝ, 0 < δ → ∃ S : E →L[ℝ] E,
    FiniteDimensional ℝ (LinearMap.range S.toLinearMap) ∧
    ∀ x ∈ M, ‖S x - x‖ < δ

def MainTarget [CompleteSpace E] [Nontrivial E] : Prop :=
  ApproximationProperty E →
    (KConvex E ↔ FiniteCotype E ∧ FiniteCotype (E →L[ℝ] ℝ))

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

def mainTarget_proved_statement : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X],
    MainTarget X

end Cotype

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.Cotype.mainTarget_proved_statement.{u}

end Problem

/- Formalization scope, from lean/docs/326.md: The cotype–cotype problem asks whether finite cotype of a Banach space and its dual characterizes $K$-convexity. The formalized result establishes this equivalence for every nonzero real Banach space with the approximation property: $X$ is $K$-convex exactly when both $X$ and $X^*$ have finite cotype. -/
