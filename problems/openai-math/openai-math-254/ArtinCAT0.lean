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

- problem_id: ArtinCAT0
- collection: openai-math
- question_id: openai-math:254
- source: openai-math
- source_locator: lean/ComparatorChallenges/ArtinCAT0.lean#OAI.ArtinCAT0.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: The Salvetti complex of every finite-rank Artin group is aspherical, proving the Artin $`K(\pi,1)`$ conjecture. Arbitrary intersections of its parabolic subgroups are parabolic, proving the Parabolic Intersection Conjecture. An explicit Artin group admits no proper cocompact isometric action on any nonempty proper CAT$`(0)`$ space. ([Lean](lean/docs/254.md)) We prove that the standard Salvetti complex of every Artin group with finitely many standard generators is aspherical. This resolves the Artin $`K(\pi,1)`$ conjecture in finite rank. We construct an Artin group on 116 generators that admits no proper, cocompact isometric action on a nonempty proper CAT(0) space. This refutes the CAT(0) conjecture for Artin groups. We prove that every intersection of parabolic subgroups of any finite-rank Artin group, with arbitrary finite or infinite Coxeter labels, is parabolic. This resolves the Parabolic Intersection Conjecture affirmatively.
- notes: OpenAI math result family 254, Classifying spaces and geometric obstructions for Artin groups -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/254.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ArtinCAT0.main
- source_theorem_count: 1
- source_solution_module: OAI.GroupTheory.ArtinCAT0.Main
- source_main_result: OAI.ArtinCAT0.main
- source_papers: preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf preprints/An-Artin-group-with-no-geometric-CAT-0-action-September-23-2026/paper.pdf preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf
- source_scope_note: lean/docs/254.md
- source_field: GroupTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace ArtinCAT0

universe uS uG uX

abbrev Letters := Fin 116
abbrev Label := WithTop ℕ

def blockLetter (b : Fin 3) (i : Fin 39) : Letters :=
  if h₀ : i.val = 0 then ⟨b.val, by omega⟩
  else if h₁ : i.val = 1 then ⟨(b.val + 1) % 3, by omega⟩
  else ⟨5 + 37 * b.val + (i.val - 2), by omega⟩

def Adjacent (s t : Letters) : Prop :=
  ∃ (b : Fin 3) (i j : Fin 39), s = blockLetter b i ∧ t = blockLetter b j ∧
    (i.val + 1 = j.val ∨ j.val + 1 = i.val)

def Distant (s t : Letters) : Prop :=
  ∃ (b : Fin 3) (i j : Fin 39), s = blockLetter b i ∧ t = blockLetter b j ∧
    (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val)

def Sentinel (s t : Letters) : Prop :=
  ((s.val = 3 ∨ s.val = 4) ∧ t.val < 3) ∨
  ((t.val = 3 ∨ t.val = 4) ∧ s.val < 3)

noncomputable def explicitMatrix (s t : Letters) : Label := by
  classical
  exact if s = t then 1 else if Adjacent s t then 3
    else if Distant s t ∨ Sentinel s t then 2 else ⊤

def alternating {S : Type uS} (s t : S) : ℕ → FreeGroup S
  | 0 => 1
  | n + 1 => FreeGroup.of s * alternating t s n

def artinRelators {S : Type uS} (M : S → S → Label) : Set (FreeGroup S) :=
  {w | ∃ (s t : S) (n : ℕ), M s t = (n : Label) ∧
    w = alternating s t n * (alternating t s n)⁻¹}

abbrev ArtinGroup {S : Type uS} (M : S → S → Label) := PresentedGroup (artinRelators M)

def Segment {X : Type uX} [MetricSpace X] (x y : X) (γ : ℝ → X) : Prop :=
  γ 0 = x ∧ γ 1 = y ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y

def CAT0 (X : Type uX) [MetricSpace X] : Prop :=
  (∀ x y : X, ∃ γ : ℝ → X, Segment x y γ) ∧
  ∀ (x y z : X) (γ η : ℝ → X), Segment x y γ → Segment x z η →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      dist (γ t) (η u) ^ 2 ≤
        (t ^ 2 - t * u) * dist x y ^ 2 +
        (u ^ 2 - t * u) * dist x z ^ 2 + t * u * dist y z ^ 2

def GeometricAction (G : Type uG) (X : Type uX) [Group G] [MetricSpace X] [MulAction G X] : Prop :=
  CAT0 X ∧
  (∀ g : G, Isometry (fun x : X => g • x)) ∧
  (∀ K : Set X, IsCompact K → {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite) ∧
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, ∃ k ∈ K, g • k = x

universe u

def main_statement : Prop :=
  (∀ s t : Letters, explicitMatrix s t = explicitMatrix t s) ∧
    (∀ s : Letters, explicitMatrix s s = 1) ∧
    (∀ s t : Letters, s ≠ t →
      explicitMatrix s t = 2 ∨ explicitMatrix s t = 3 ∨ explicitMatrix s t = ⊤) ∧
    (∀ (X : Type u) [MetricSpace X] [ProperSpace X] [Nonempty X]
      [MulAction (ArtinGroup explicitMatrix) X],
      ¬ GeometricAction (ArtinGroup explicitMatrix) X)

end ArtinCAT0

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.ArtinCAT0.main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/254.md: The Artin $K(\pi,1)$ conjecture asserts that the standard Salvetti complex of every finite-rank Artin group is aspherical. The formalized result proves the equivalent statement that its universal cover is contractible. It applies to every Coxeter matrix on a finite generating set, including empty and disconnected diagrams and infinite edge labels. The associated Coxeter and Artin groups may be infinite. Later corollaries in the manuscript are not included. The geometric-action question asks whether every Artin group acts properly and cocompactly by isometries on a proper CAT(0) space. The formalized result gives a counterexample: an Artin group defined by a symmetric matrix on $116$ generators, with diagonal entries $1$ and off-diagonal entries in $\{2,3,\infty\}$. It admits no such action on any nonempty proper CAT(0) space, in any dimension. The formalization proves that the intersection of any family of parabolic subgroups of a finite-rank Artin group is parabolic. Every such intersection is already the intersection of at most the rank many members, and every subset has a unique parabolic closure. Both finite and infinite Coxeter labels are allowed. For irreducible Artin groups with an infinite Coxeter label, it also proves acylindrical hyperbolicity and weak malnormality of every proper parabolic subgroup. These are the intersection and structural consequences selected from the paper. -/
