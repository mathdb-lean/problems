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

- problem_id: PeriodicGroup
- collection: openai-math
- question_id: openai-math:247
- source: openai-math
- source_locator: lean/ComparatorChallenges/PeriodicGroup.lean#OAI.SourceBurnside.thm_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs an infinite finitely presented residually finite group whose elements all have finite 2-power order, answering the finitely presented Burnside problem negatively even in this class. The construction also yields an infinite-dimensional finitely presented nil associative 𝔽2-algebra and a finitely presented infinite-dimensional algebraic unitization, giving negative answers to the corresponding nilpotence and Kurosh finiteness questions. ([Lean](lean/docs/247.md)) We construct an infinite group with an ordinary finite presentation in which every element has finite order, answering the finitely presented Burnside question negatively. We also construct an infinite-dimensional finitely presented nonunital nil associative algebra over 𝔽2 that is Jacobson radical but not nilpotent. Its unitization is finitely presented, algebraic, and infinite-dimensional. These algebras answer the finitely presented nil- and radical-algebra nilpotence questions and the finite-presentation version of Kurosh's algebraic finiteness question negatively.
- notes: OpenAI math result family 247, An infinite finitely presented residually finite 2-group and a finitely presented nil algebra -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/247.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SourceBurnside.thm_main
- source_theorem_count: 1
- source_solution_module: OAI.GroupTheory.PeriodicGroups.Main
- source_papers: preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf
- source_scope_note: lean/docs/247.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

universe u

namespace SourceBurnside

structure Root (n : ℕ) where
  row : Fin n
  col : Fin n
  ne : row ≠ col
  deriving DecidableEq

abbrev Generator (n : ℕ) (R : Type u) := Root n × R

def bracket {G : Type u} [Group G] (x y : G) : G := x * y * x⁻¹ * y⁻¹

def letter {n : ℕ} {R : Type u} (p : Root n) (a : R) :
    FreeGroup (Generator n R) := FreeGroup.of (p, a)

inductive SteinbergRel (n : ℕ) (R : Type u) [Ring R] :
    FreeGroup (Generator n R) → Prop
  | add (p : Root n) (a b : R) :
      SteinbergRel n R (letter p (a + b) * (letter p a * letter p b)⁻¹)
  | commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col) (a b : R) :
      SteinbergRel n R (bracket (letter p a) (letter q b))
  | mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
      SteinbergRel n R
        (bracket (letter ⟨i, j, hij⟩ a) (letter ⟨j, k, hjk⟩ b) *
          (letter ⟨i, k, hik⟩ (a * b))⁻¹)

def Steinberg (n : ℕ) (R : Type u) [Ring R] :=
  PresentedGroup {r | SteinbergRel n R r}
  deriving Group

def Periodic (G : Type u) [Group G] : Prop := ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1

def MainStatement : Prop :=
  ∃ (R : Type) (_ : Ring R) (_ : Algebra (ZMod 2) R),
    Infinite (Steinberg 12 R) ∧ Group.IsFinitelyPresented (Steinberg 12 R) ∧
      Periodic (Steinberg 12 R)

def BurnsideStatement : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧ Group.IsFinitelyPresented G ∧ Periodic G

end SourceBurnside

namespace SourceBurnside

def thm_main_statement : Prop :=
  MainStatement ∧ BurnsideStatement

end SourceBurnside

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SourceBurnside.thm_main_statement

end Problem

/- Formalization scope, from lean/docs/247.md: The finitely presented Burnside question asks whether a finitely presented group in which every element has finite order must be finite. The formalization gives a negative answer by constructing an infinite finitely presented periodic group, including a witness realized as a Steinberg group over an algebra of characteristic two. Periodicity means that each element has some finite order; no common exponent is asserted. The paper's separate nil-algebra and radical-algebra conclusions are outside these selected statements. -/
