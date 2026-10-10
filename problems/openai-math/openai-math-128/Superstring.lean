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

- problem_id: Superstring
- collection: openai-math
- question_id: openai-math:128
- source: openai-math
- source_locator: lean/ComparatorChallenges/Superstring.lean#OAI.Superstring.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives a deterministic polynomial-time algorithm constructing a common superstring of length at most twice the optimum for every finite family of explicitly represented strings. The running time is polynomial in the full encoded input length, including symbol labels. ([Lean](lean/docs/128.md)) We give a deterministic algorithm that, for every finite family of explicitly represented ordinary strings, outputs a common superstring of length at most twice the optimum in time polynomial in the total encoded input size, including symbol labels. The guarantee applies to the algorithm constructed here, not the classical maximum-overlap Greedy procedure.
- notes: OpenAI math result family 128, A factor-two approximation for shortest common superstring -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/128.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Superstring.main
- source_theorem_count: 1
- source_solution_module: OAI.Computability.Superstring.Main
- source_main_result: OAI.Superstring.main
- source_papers: preprints/A-Polynomial-Time-2-Approximation-for-Shortest-Common-Superstring-September-24-2026/paper.pdf
- source_scope_note: lean/docs/128.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Superstring

abbrev Symbol := List Bool
abbrev Word := List Symbol
abbrev Instance := List Word

/-- Prefix markers encode the list spine, including its final boundary. -/
def encodeList {α : Type} (enc : α → List Bool) : List α → List Bool
  | [] => [true]
  | a :: as => false :: (enc a ++ encodeList enc as)

def encodeSymbol : Symbol → List Bool := encodeList (fun b => [b])
def encodeWord : Word → List Bool := encodeList encodeSymbol
def encodeInstance : Instance → List Bool := encodeList encodeWord

/-- Ordinary contiguous substring containment, including the empty word. -/
def IsCommonSuperstring (S : Instance) (T : Word) : Prop :=
  ∀ s ∈ S, s <:+: T

/-- The optimum in symbols, not in bits. -/
noncomputable def opt (S : Instance) : ℕ :=
  sInf {n : ℕ | ∃ T : Word, IsCommonSuperstring S T ∧ T.length = n}

/-- A deterministic finite-stack-machine implementation, with a polynomial bound
on bit-level running time in the explicitly encoded input length. -/
def HasPolynomialImplementation (f : Instance → Word) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime encodeInstance encodeWord f,
    ∀ k : M.tm.K, Finite (M.tm.Γ k)

/-- The deterministic algorithm with its exact finite-alphabet bit-machine
certificate, contiguous coverage, and factor-two bound in symbols. -/
def main_statement : Prop :=
  ∃ f : Instance → Word,
    HasPolynomialImplementation f ∧
    ∀ S, IsCommonSuperstring S (f S) ∧ (f S).length ≤ 2 * opt S

end Superstring

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Superstring.main_statement

end Problem

/- Formalization scope, from lean/docs/128.md: The shortest common superstring problem asks for the shortest string containing each input string as a contiguous substring. The formalized result gives one deterministic polynomial-time algorithm whose output is a common superstring of length at most twice the unrestricted optimum. It applies to every finite list of explicitly encoded strings, with running time measured in input bits and the approximation ratio measured in symbol length. -/
