import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
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

- problem_id: KaplanskyQuasitrace
- collection: openai-math
- question_id: openai-math:294
- source: openai-math
- source_locator: lean/ComparatorChallenges/KaplanskyQuasitrace.lean#OAI.Kaplansky.kaplansky_quasitrace_counterexample
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves Kaplansky's quasitrace conjecture by constructing a separable unital complex C∗-algebra admitting normalized 2-quasitraces, all of which are nonadditive. As a consequence, two unital simple stably finite C∗-algebras can have a properly infinite minimal tensor product, with one factor $`C_r^*(\mathbb F_2)`$. ([Lean](lean/docs/294.md)) We refute Kaplansky's quasitrace conjecture by constructing a separable unital complex C∗-algebra that admits normalized 2-quasitraces but has no tracial state. As a consequence, we show that the minimal tensor product of two unital simple stably finite complex C∗-algebras can be properly infinite, even when one factor is the reduced free-group algebra $`C_r^*(\mathbb F_2)`$.
- notes: OpenAI math result family 294, Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/294.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Kaplansky.kaplansky_quasitrace_counterexample
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Kaplansky.Main
- source_main_result: OAI.Kaplansky.kaplansky_quasitrace_counterexample
- source_papers: preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/294.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped ComplexOrder

namespace Kaplansky

variable {A : Type*} [CStarAlgebra A]

structure OneQuasitrace (A : Type*) [CStarAlgebra A] where
  toFun : A → ℂ
  square_nonneg : ∀ x, 0 ≤ toFun (star x * x)
  square_swap : ∀ x, toFun (star x * x) = toFun (x * star x)
  real_imag : ∀ h k, IsSelfAdjoint h → IsSelfAdjoint k →
    toFun (h + Complex.I • k) = toFun h + Complex.I * toFun k
  abelian_linear : ∀ S : NonUnitalStarSubalgebra ℂ A,
    IsClosed (S : Set A) → (∀ x y : S, x * y = y * x) →
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = toFun x

instance : CoeFun (OneQuasitrace A) (fun _ => A → ℂ) := ⟨OneQuasitrace.toFun⟩

def OneQuasitrace.Normalized (τ : OneQuasitrace A) : Prop := τ 1 = 1

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

def upperLeft (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix fun i j => if i = 0 ∧ j = 0 then a else 0

def OneQuasitrace.IsTwo (τ : OneQuasitrace A) : Prop :=
  ∃ σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A), ∀ a, σ (upperLeft a) = τ a

def PositiveContraction (a : A) : Prop := (∃ x, a = star x * x) ∧ ‖a‖ ≤ 1

def MainTarget : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI := inst
    TopologicalSpace.SeparableSpace A ∧
    (∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo) ∧
    ∃ a b : A, PositiveContraction a ∧ PositiveContraction b ∧
      ∀ τ : OneQuasitrace A, τ.Normalized → τ.IsTwo →
        (1 : ℝ) / 144 ≤ (τ (a+b) - τ a - τ b).re

def kaplansky_quasitrace_counterexample_statement : Prop :=
  MainTarget

end Kaplansky

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Kaplansky.kaplansky_quasitrace_counterexample_statement

end Problem

/- Formalization scope, from lean/docs/294.md: Kaplansky's quasitrace conjecture predicts that every $2$-quasitrace on a $C^*$-algebra is a trace. The formalization constructs a separable $C^*$-algebra with normalized $2$-quasitraces and fixed positive contractions $a,b$ for which every such quasitrace satisfies $\mathrm{Re}(\tau(a+b)-\tau(a)-\tau(b))\ge1/144$. Thus none is additive on this pair. The formalization also gives simple stably finite $C^*$-algebras whose spatial tensor product is properly infinite, a separable stably finite algebra with no tracial state, and a tensor-product example in which normalized $2$-quasitraces are lost. These are the stable-finiteness consequences named in the paper's title. -/
