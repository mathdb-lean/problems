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

- problem_id: ArtinParabolicIntersections
- collection: openai-math
- question_id: openai-math:254
- source: openai-math
- source_locator: lean/ComparatorChallenges/ArtinParabolicIntersections.lean#OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: The Salvetti complex of every finite-rank Artin group is aspherical, proving the Artin $`K(\pi,1)`$ conjecture. Arbitrary intersections of its parabolic subgroups are parabolic, proving the Parabolic Intersection Conjecture. An explicit Artin group admits no proper cocompact isometric action on any nonempty proper CAT$`(0)`$ space. ([Lean](lean/docs/254.md)) We prove that the standard Salvetti complex of every Artin group with finitely many standard generators is aspherical. This resolves the Artin $`K(\pi,1)`$ conjecture in finite rank. We construct an Artin group on 116 generators that admits no proper, cocompact isometric action on a nonempty proper CAT(0) space. This refutes the CAT(0) conjecture for Artin groups. We prove that every intersection of parabolic subgroups of any finite-rank Artin group, with arbitrary finite or infinite Coxeter labels, is parabolic. This resolves the Parabolic Intersection Conjecture affirmatively.
- notes: OpenAI math result family 254, Classifying spaces and geometric obstructions for Artin groups -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/254.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics
- source_theorem_count: 4
- source_solution_module: OAI.Topology.ArtinGroups.ParabolicIntersections.Main
- source_papers: preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf preprints/An-Artin-group-with-no-geometric-CAT-0-action-September-23-2026/paper.pdf preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf
- source_scope_note: lean/docs/254.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Parabolic intersections, parabolic closure, and non-clique Artin-group dynamics. -/

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

def artinParabolic (M : CoxeterMatrix S) (T : Set S) : Subgroup (Artin M) :=
  Subgroup.closure (generator M '' T)

end HarmonicArtin

namespace HarmonicArtin.ParabolicIntersections

variable {G : Type*} [Group G]

/-- `g P g⁻¹`, with membership expressed without existential witnesses. -/
def conjugate (g : G) (P : Subgroup G) : Subgroup G :=
  P.comap (MulAut.conj g⁻¹).toMonoidHom

variable {S : Type*} (M : CoxeterMatrix S)

/-- Conjugates of standard subgroups, with no spherical-type restriction. -/
def IsParabolic (P : Subgroup (Artin M)) : Prop :=
  ∃ (X : Set S) (g : Artin M), P = conjugate g (artinParabolic M X)

end HarmonicArtin.ParabolicIntersections

namespace HarmonicArtin.ParabolicIntersections

noncomputable def gromovProduct {X : Type} [MetricSpace X] (o x y : X) : ℝ :=
  (dist o x + dist o y - dist x y)/2

def IsGromovHyperbolic (X : Type) [MetricSpace X] : Prop :=
  ∃ δ : ℝ, 0 ≤ δ ∧ ∀ o x y z : X,
    min (gromovProduct o x y) (gromovProduct o y z) ≤ gromovProduct o x z + δ

def IsGeodesicMetric (X : Type) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : Set.Icc (0 : ℝ) (dist x y) → X,
    Isometry γ ∧ γ ⟨0,le_rfl,dist_nonneg⟩=x ∧ γ ⟨dist x y,dist_nonneg,le_rfl⟩=y

def IsGromovSequence {X : Type} [MetricSpace X] (o : X) (u : ℕ → X) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n → R ≤ gromovProduct o (u m) (u n)

def IsAcylindrical (G X : Type) [Group G] [MetricSpace X] [MulAction G X] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∃ N : ℕ, ∀ x y : X, R ≤ dist x y →
    {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.Finite ∧
      {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.ncard ≤ N

def HasThreeOrbitLimitPoints (G X : Type) [Group G] [MetricSpace X] [MulAction G X] : Prop :=
  ∃ o : X, ∃ u : Fin 3 → ℕ → G,
    (∀ i, IsGromovSequence o (fun n => u i n • o)) ∧
    ∀ i j, i ≠ j → ∃ B : ℝ, ∀ m n, gromovProduct o (u i m • o) (u j n • o) ≤ B

/-- An isometric non-elementary acylindrical action on a geodesic
Gromov-hyperbolic metric space. -/
def AcylindricallyHyperbolic (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (metric : MetricSpace X) (action : MulAction G X),
    @IsGeodesicMetric X metric ∧ @IsGromovHyperbolic X metric ∧
    (∀ g : G, @Isometry X X metric.toPseudoMetricSpace.toPseudoEMetricSpace metric.toPseudoMetricSpace.toPseudoEMetricSpace
      (fun x => @SMul.smul G X action.toSMul g x)) ∧
    @IsAcylindrical G X _ metric action ∧ @HasThreeOrbitLimitPoints G X _ metric action

def WeaklyMalnormal {G : Type} [Group G] (P : Subgroup G) : Prop :=
  ∃ g : G, (↑(P ⊓ conjugate g P) : Set G).Finite

variable {S : Type} (M : CoxeterMatrix S)

/-- No nontrivial partition has every cross label equal to two. -/
def IsIrreducible : Prop :=
  ∀ Y : Set S, Y.Nonempty → Yᶜ.Nonempty → ∃ s ∈ Y, ∃ t ∉ Y, M s t ≠ 2

end HarmonicArtin.ParabolicIntersections

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The intersection of two conjugates of standard parabolics is parabolic. -/
def unconditional_parabolic_intersections_statement : Prop :=
  ∀ {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (X Y : Set S) (g h : Artin M),
    ∃ (Z : Set S) (k : Artin M),
      conjugate g (artinParabolic M X) ⊓ conjugate h (artinParabolic M Y) =
        conjugate k (artinParabolic M Z)

/-- An arbitrary parabolic intersection is obtained from at most the rank many members. -/
def unconditional_arbitrary_intersections_statement : Prop :=
  ∀ {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P),
    (∃ F₀ : Finset (Subgroup (Artin M)),
      (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ Nat.card S ∧
        sInf F = sInf (↑F₀ : Set (Subgroup (Artin M)))) ∧ IsParabolic M (sInf F)

/-- Every subset is contained in a unique smallest parabolic subgroup. -/
def unconditional_parabolic_closure_statement : Prop :=
  ∀ {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (E : Set (Artin M)),
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q

/-- An irreducible non-clique Artin group has an acylindrical non-elementary
hyperbolic action and all its proper parabolics are weakly malnormal. -/
def unconditional_nonclique_dynamics_statement : Prop :=
  ∀ {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (hIrred : IsIrreducible M) (hInf : ∃ s t : S, s ≠ t ∧ M s t = 0),
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M), IsParabolic M P → P ≠ ⊤ → WeaklyMalnormal P

end HarmonicArtin.ParabolicIntersections

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections_statement ∧
  _root_.OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections_statement ∧
  _root_.OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure_statement ∧
  _root_.OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics_statement

end Problem

/- Formalization scope, from lean/docs/254.md: The Artin $K(\pi,1)$ conjecture asserts that the standard Salvetti complex of every finite-rank Artin group is aspherical. The formalized result proves the equivalent statement that its universal cover is contractible. It applies to every Coxeter matrix on a finite generating set, including empty and disconnected diagrams and infinite edge labels. The associated Coxeter and Artin groups may be infinite. Later corollaries in the manuscript are not included. The geometric-action question asks whether every Artin group acts properly and cocompactly by isometries on a proper CAT(0) space. The formalized result gives a counterexample: an Artin group defined by a symmetric matrix on $116$ generators, with diagonal entries $1$ and off-diagonal entries in $\{2,3,\infty\}$. It admits no such action on any nonempty proper CAT(0) space, in any dimension. The formalization proves that the intersection of any family of parabolic subgroups of a finite-rank Artin group is parabolic. Every such intersection is already the intersection of at most the rank many members, and every subset has a unique parabolic closure. Both finite and infinite Coxeter labels are allowed. For irreducible Artin groups with an infinite Coxeter label, it also proves acylindrical hyperbolicity and weak malnormality of every proper parabolic subgroup. These are the intersection and structural consequences selected from the paper. -/
