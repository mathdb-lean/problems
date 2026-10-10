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

- problem_id: DepthThree
- collection: openai-math
- question_id: openai-math:112
- source: openai-math
- source_locator: lean/ComparatorChallenges/DepthThree.lean#OAI.DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a single language in deterministic polynomial time whose n-bit membership function requires $`2^{\omega(\sqrt n)}`$ total gates in unbounded-fan-in OR–AND–OR circuits, at every sufficiently large input length. This crosses the square-root-exponent threshold for explicit depth-three Boolean circuit lower bounds. ([Lean](lean/docs/112.md)) We construct a language in deterministic polynomial time whose n-bit membership function requires $`2^{\omega(\sqrt n)}`$ gates in an unbounded-fan-in OR–AND–OR circuit. The bound holds at every sufficiently large input length and counts all gates, including the bottom layer.
- notes: OpenAI math result family 112, Beyond the square-root exponent for depth-three circuits -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/112.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound
- source_theorem_count: 1
- source_solution_module: OAI.Computability.DepthThree.Main
- source_main_result: OAI.DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound
- source_papers: preprints/Beyond-the-Square-Root-Exponent-for-Depth-Three-Boolean-Circuits-September-23-2026/main.pdf
- source_scope_note: lean/docs/112.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace DepthThreeLowerBound

universe uV uS uK uGamma uQ

abbrev Cube (V : Type uV) := V → Bool
abbrev Literal (V : Type uV) := V × Bool

variable {V : Type uV}

namespace Literal

def eval (l : Literal V) (x : Cube V) : Bool := decide (x l.1 = l.2)

end Literal

abbrev GateInput (V : Type uV) := Sum (Literal V) Bool
abbrev RawClause (V : Type uV) := List (GateInput V)

namespace GateInput

def eval : GateInput V → Cube V → Bool
  | .inl l, x => l.eval x
  | .inr b, _ => b

end GateInput

namespace RawClause

noncomputable def eval (C : RawClause V) (x : Cube V) : Bool := by
  classical
  exact decide (∃ l ∈ C, l.eval x = true)

end RawClause

structure Circuit3 (V : Type uV) where
  bottomCount : ℕ
  middleCount : ℕ
  bottom : Fin bottomCount → RawClause V
  middle : Fin middleCount → Finset (Fin bottomCount)
  top : Finset (Fin middleCount)

namespace Circuit3

def gateCount (C : Circuit3 V) : ℕ := C.bottomCount + C.middleCount + 1

noncomputable def middleEval (C : Circuit3 V) (j : Fin C.middleCount)
    (x : Cube V) : Bool := by
  classical
  exact decide (∀ i ∈ C.middle j, (C.bottom i).eval x = true)

noncomputable def eval (C : Circuit3 V) (x : Cube V) : Bool := by
  classical
  exact decide (∃ j ∈ C.top, C.middleEval j x = true)

def Computes (C : Circuit3 V) (f : Cube V → Bool) : Prop := ∀ x, C.eval x = f x

end Circuit3

def runSteps {S : Type uS} (step : S → Option S) (n : ℕ) (c : Option S) : Option S :=
  (fun oc => oc.bind step)^[n] c

inductive HeadMove
  | left
  | stay
  | right

def HeadMove.apply {Γ : Type uGamma} [Inhabited Γ] : HeadMove → Turing.Tape Γ → Turing.Tape Γ
  | .left, t => t.move Turing.Dir.left
  | .stay, t => t
  | .right, t => t.move Turing.Dir.right

structure MultiTapeCfg (K : Type uK) (Γ : Type uGamma) (Q : Type uQ) [Inhabited Γ] where
  q : Q
  tapes : K → Turing.Tape Γ

abbrev MultiTapeCode (K : Type uK) (Γ : Type uGamma) (Q : Type uQ) :=
  Q → (K → Γ) → Option (Q × (K → Γ) × (K → HeadMove))

def multiTapeUpdate {K : Type uK} {Γ : Type uGamma} {Q : Type uQ} [Inhabited Γ] (c : MultiTapeCfg K Γ Q)
    (q : Q) (writes : K → Γ) (moves : K → HeadMove) : MultiTapeCfg K Γ Q :=
  ⟨q, fun k => (moves k).apply ((c.tapes k).write (writes k))⟩

def multiTapeStep {K : Type uK} {Γ : Type uGamma} {Q : Type uQ} [Inhabited Γ] (code : MultiTapeCode K Γ Q)
    (c : MultiTapeCfg K Γ Q) : Option (MultiTapeCfg K Γ Q) :=
  (code c.q (fun k => (c.tapes k).head)).map fun out =>
    multiTapeUpdate c out.1 out.2.1 out.2.2

structure FiniteMultiTapeMachine where
  K : Type
  [tapeFinite : Fintype K]
  [tapeDecidableEq : DecidableEq K]
  inputTape : K
  Γ : Type
  [alphabetInhabited : Inhabited Γ]
  [alphabetFinite : Fintype Γ]
  Q : Type
  [stateFinite : Fintype Q]
  initialState : Q
  inputSymbol : Bool → Γ
  input_injective : Function.Injective inputSymbol
  input_ne_blank : ∀ b, inputSymbol b ≠ default
  code : MultiTapeCode K Γ Q
  accept : Q → Bool

attribute [instance] FiniteMultiTapeMachine.tapeFinite
  FiniteMultiTapeMachine.tapeDecidableEq FiniteMultiTapeMachine.alphabetInhabited
  FiniteMultiTapeMachine.alphabetFinite FiniteMultiTapeMachine.stateFinite

namespace FiniteMultiTapeMachine

abbrev Cfg (M : FiniteMultiTapeMachine) := MultiTapeCfg M.K M.Γ M.Q

abbrev step (M : FiniteMultiTapeMachine) : M.Cfg → Option M.Cfg :=
  multiTapeStep M.code

def init (M : FiniteMultiTapeMachine) (input : List Bool) : M.Cfg :=
  ⟨M.initialState, fun k =>
    if k = M.inputTape then Turing.Tape.mk₁ (input.map M.inputSymbol)
    else Turing.Tape.mk₁ []⟩

end FiniteMultiTapeMachine

def MultiTapeHaltsIn (M : FiniteMultiTapeMachine) (input : List Bool)
    (output : Bool) (time : ℕ) : Prop :=
  ∃ k ≤ time, ∃ c : M.Cfg,
    runSteps M.step k (some (M.init input)) = some c ∧
    M.step c = none ∧ M.accept c.q = output

def exists_polynomial_time_language_depth_three_lower_bound_statement : Prop :=
  ∃ (L : List Bool → Bool) (M : FiniteMultiTapeMachine) (C a : ℕ),
      0 < C ∧ 0 < a ∧
      (∀ w : List Bool, MultiTapeHaltsIn M w (L w) (C * (w.length + 1) ^ a)) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Circuit3 (Fin n), D.Computes (fun x => L (List.ofFn x)) →
          (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) < (D.gateCount : ℝ)

end DepthThreeLowerBound

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound_statement

end Problem

/- Formalization scope, from lean/docs/112.md: The formalized result gives one polynomial-time Boolean language whose exact depth-three OR–AND–OR circuit size eventually exceeds $2^{A\sqrt n}$ for every fixed $A>0$. The language and its polynomial-time algorithm are fixed before $A$ is chosen, while circuits may vary with the input length. Gates have unrestricted finite fan-in and sharing, with free input negations and constants. The result does not assert a fixed exponent $n^{1/2+\varepsilon}$ or a lower bound for unrestricted depth. -/
