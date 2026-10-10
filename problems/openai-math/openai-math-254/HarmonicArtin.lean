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

- problem_id: HarmonicArtin
- collection: openai-math
- question_id: openai-math:254
- source: openai-math
- source_locator: lean/ComparatorChallenges/HarmonicArtin.lean#OAI.HarmonicArtin.salvetti_cover_contractible
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: The Salvetti complex of every finite-rank Artin group is aspherical, proving the Artin $`K(\pi,1)`$ conjecture. Arbitrary intersections of its parabolic subgroups are parabolic, proving the Parabolic Intersection Conjecture. An explicit Artin group admits no proper cocompact isometric action on any nonempty proper CAT$`(0)`$ space. ([Lean](lean/docs/254.md)) We prove that the standard Salvetti complex of every Artin group with finitely many standard generators is aspherical. This resolves the Artin $`K(\pi,1)`$ conjecture in finite rank. We construct an Artin group on 116 generators that admits no proper, cocompact isometric action on a nonempty proper CAT(0) space. This refutes the CAT(0) conjecture for Artin groups. We prove that every intersection of parabolic subgroups of any finite-rank Artin group, with arbitrary finite or infinite Coxeter labels, is parabolic. This resolves the Parabolic Intersection Conjecture affirmatively.
- notes: OpenAI math result family 254, Classifying spaces and geometric obstructions for Artin groups -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/254.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.HarmonicArtin.salvetti_cover_contractible
- source_theorem_count: 1
- source_solution_module: OAI.Topology.ArtinGroups.Main
- source_main_result: OAI.HarmonicArtin.salvetti_cover_contractible
- source_papers: preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf preprints/An-Artin-group-with-no-geometric-CAT-0-action-September-23-2026/paper.pdf preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf
- source_scope_note: lean/docs/254.md
- source_field: Topology
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace HarmonicArtin

universe u

variable {S : Type u}

def alternating (s t : S) : ℕ → FreeGroup S
  | 0 => 1
  | n + 1 => FreeGroup.of s * alternating t s n

def braidRelators (M : CoxeterMatrix S) : Set (FreeGroup S) :=
  Set.range fun st : S × S =>
    alternating st.1 st.2 (M st.1 st.2) *
      (alternating st.2 st.1 (M st.1 st.2))⁻¹

abbrev Artin (M : CoxeterMatrix S) := PresentedGroup (braidRelators M)

def generator (M : CoxeterMatrix S) (s : S) : Artin M := PresentedGroup.of s

def coxeterParabolic (M : CoxeterMatrix S) (T : Set S) : Subgroup M.Group :=
  Subgroup.closure (M.simple '' T)

def IsSpherical (M : CoxeterMatrix S) (T : Set S) : Prop :=
  Finite (coxeterParabolic M T)

abbrev SphericalType (M : CoxeterMatrix S) := {T : Set S // IsSpherical M T}

abbrev LiftedCell (M : CoxeterMatrix S) := Artin M × SphericalType M

def wordArtin (M : CoxeterMatrix S) (w : List S) : Artin M :=
  (w.map (generator M)).prod

def wordCoxeter (M : CoxeterMatrix S) (w : List S) : M.Group :=
  (w.map M.simple).prod

def LiftedFace (M : CoxeterMatrix S) (a b : LiftedCell M) : Prop :=
  a.2.1 ⊆ b.2.1 ∧ ∃ w : List S,
    (∀ s ∈ w, s ∈ b.2.1) ∧
    M.toCoxeterSystem.length (wordCoxeter M w) = w.length ∧
    (∀ v : coxeterParabolic M a.2.1,
      M.toCoxeterSystem.length (wordCoxeter M w) ≤
        M.toCoxeterSystem.length (wordCoxeter M w * v)) ∧
    a.1 = b.1 * wordArtin M w

instance (M : CoxeterMatrix S) : Preorder (LiftedCell M) where
  le := Relation.ReflTransGen (LiftedFace M)
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

noncomputable def SalvettiCover (M : CoxeterMatrix S) : TopCat :=
  SSet.toTop.obj (CategoryTheory.nerve (LiftedCell M))

/-- The full lifted spherical-cell realization is contractible for every
Coxeter matrix with finitely many standard generators. -/
def salvetti_cover_contractible_statement : Prop :=
  ∀ {S : Type u} [Finite S] (M : CoxeterMatrix S),
    ContractibleSpace (SalvettiCover M)

end HarmonicArtin

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.HarmonicArtin.salvetti_cover_contractible_statement.{u}

end Problem

/- Formalization scope, from lean/docs/254.md: The Artin $K(\pi,1)$ conjecture asserts that the standard Salvetti complex of every finite-rank Artin group is aspherical. The formalized result proves the equivalent statement that its universal cover is contractible. It applies to every Coxeter matrix on a finite generating set, including empty and disconnected diagrams and infinite edge labels. The associated Coxeter and Artin groups may be infinite. Later corollaries in the manuscript are not included. The geometric-action question asks whether every Artin group acts properly and cocompactly by isometries on a proper CAT(0) space. The formalized result gives a counterexample: an Artin group defined by a symmetric matrix on $116$ generators, with diagonal entries $1$ and off-diagonal entries in $\{2,3,\infty\}$. It admits no such action on any nonempty proper CAT(0) space, in any dimension. The formalization proves that the intersection of any family of parabolic subgroups of a finite-rank Artin group is parabolic. Every such intersection is already the intersection of at most the rank many members, and every subset has a unique parabolic closure. Both finite and infinite Coxeter labels are allowed. For irreducible Artin groups with an infinite Coxeter label, it also proves acylindrical hyperbolicity and weak malnormality of every proper parabolic subgroup. These are the intersection and structural consequences selected from the paper. -/
