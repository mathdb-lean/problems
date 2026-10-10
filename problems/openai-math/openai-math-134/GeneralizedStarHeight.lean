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

- problem_id: GeneralizedStarHeight
- collection: openai-math
- question_id: openai-math:134
- source: openai-math
- source_locator: lean/ComparatorChallenges/GeneralizedStarHeight.lean#OAI.GeneralizedStarHeight.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Every regular language over a finite alphabet has a generalized regular expression with at most three nested Kleene stars, allowing union, concatenation and complement over the same alphabet. This establishes an absolute bound independent of automaton size, resolving the uniform-boundedness version of the generalized star-height problem. ([Lean](lean/docs/134.md)) Every regular language over a finite alphabet has a generalized regular expression of star height at most thirteen over that same alphabet. We prove this uniform bound by representing finite monoid computations as affine updates and recovering them through twelve successive split constructions. Every regular language over a finite alphabet has generalized star height at most four over that same alphabet. We give a complete construction using an affine correction that hides one interval product, a finite clock, and several scales for moving boundaries through periodic words. Every regular language over a finite alphabet has generalized star height at most three, with complement taken in the same free monoid. We express finite-monoid computations using a prefix code of word pieces.
- notes: OpenAI math result family 134, Generalized star height at most three -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/134.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.GeneralizedStarHeight.main
- source_theorem_count: 1
- source_solution_module: OAI.Computability.StarHeight.Main
- source_papers: preprints/Finite-Monoid-Computations-and-a-Uniform-Generalized-Star-Height-Bound-September-25-2026/Finite-Monoid-Computations-and-a-Uniform-Generalized-Star-Height-Bound-September-25-2026.pdf preprints/Generalized-Star-Height-at-Most-Four-September-25-2026/Generalized-Star-Height-at-Most-Four-September-25-2026.pdf preprints/Generalized-Star-Height-at-Most-Three-September-25-2026/article.pdf
- source_scope_note: lean/docs/134.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace GeneralizedStarHeight

universe u

inductive Expression (Alphabet : Type u) : Type u
  | zero : Expression Alphabet
  | one : Expression Alphabet
  | letter : Alphabet → Expression Alphabet
  | union : Expression Alphabet → Expression Alphabet → Expression Alphabet
  | concat : Expression Alphabet → Expression Alphabet → Expression Alphabet
  | compl : Expression Alphabet → Expression Alphabet
  | star : Expression Alphabet → Expression Alphabet

namespace Expression

open scoped Computability

def language {Alphabet : Type u} : Expression Alphabet → Language Alphabet
  | .zero => 0
  | .one => 1
  | .letter a => {[a]}
  | .union P Q => P.language + Q.language
  | .concat P Q => P.language * Q.language
  | .compl P => P.languageᶜ
  | .star P => P.language∗

def height {Alphabet : Type u} : Expression Alphabet → ℕ
  | .zero | .one | .letter _ => 0
  | .union P Q | .concat P Q => max P.height Q.height
  | .compl P => P.height
  | .star P => 1 + P.height

end Expression

def HasHeightAtMost {Alphabet : Type u} (L : Language Alphabet) (n : ℕ) : Prop :=
  ∃ P : Expression Alphabet, P.language = L ∧ P.height ≤ n

def main_statement : Prop :=
  ∀ {Alphabet : Type u} [Finite Alphabet] (L : Language Alphabet) (hL : L.IsRegular),
    HasHeightAtMost L 3

end GeneralizedStarHeight

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.GeneralizedStarHeight.main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/134.md: Generalized star height measures the nesting of Kleene stars in regular expressions that also allow Boolean operations. The formalization proves that every regular language over a finite alphabet has a generalized expression over the same alphabet of star height at most three. This is stronger than the bound of thirteen in the accompanying finite-monoid paper. The selected statement asserts the uniform expression bound, without separately encoding every construction step of that paper. The formalization proves that every regular language over a finite alphabet has a generalized regular expression over that same alphabet with star height at most three. Generalized expressions allow Boolean operations as well as concatenation and Kleene star. The bound of three implies the accompanying paper's bound of four; the selected statement concerns the expression bound itself. Generalized star height measures the nesting of Kleene stars in regular expressions that also allow Boolean operations. The formalization proves that every regular language over a finite alphabet has a generalized regular expression over that same alphabet of star height at most three. Complements are taken in the same free monoid. This is the paper's uniform bound. -/
