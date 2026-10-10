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

- problem_id: HyperbolicObstruction
- collection: openai-math
- question_id: openai-math:257
- source: openai-math
- source_locator: lean/ComparatorChallenges/HyperbolicObstruction.lean#OAI.HyperbolicObstruction.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Answers negatively whether every word-hyperbolic group is a CAT(0) group. Constructs one with a finite classifying space but no proper cocompact isometric action on any proper complete $`\mathop{\mathrm{CAT}}\nolimits (0)`$ space, in any dimension. ([Lean](lean/docs/257.md)) We construct a hyperbolic group with a finite classifying space that admits no geometric action on a proper complete CAT(0) space. Consequently, a finite aspherical simplicial complex with a linear combinatorial disk-filling inequality need not have a finite locally CAT(0) homotopy model, and hence need not have a finite locally CAT(−1) model. Here metric models carry geodesic length metrics inducing the given complex topology.
- notes: OpenAI math result family 257, A hyperbolic group without a geometric CAT(0) action -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/257.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.HyperbolicObstruction.main
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.HyperbolicGroups.Main
- source_main_result: OAI.HyperbolicObstruction.main
- source_papers: preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf
- source_scope_note: lean/docs/257.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI



section

section

/-!
Finite complexes are standard barycentric realizations of finite abstract
simplicial complexes. Area-counted elementary edge homotopies encode the
usual triangular disk diagrams, allowing spurs and collapsed edges. Null edge
loops (equivalently closed lifts to the universal cover) are those admitting
such a disk, without any area bound. Asphericity is vanishing of all higher
homotopy groups of this finite polyhedron. The CAT conditions use the standard
squared-distance / hyperbolic-cosh comparison formulations.
-/

noncomputable section
open scoped Topology ContinuousMap

namespace HyperbolicObstruction

structure FiniteComplex where
  n : ℕ
  complex : AbstractSimplicialComplex (Fin n)

namespace FiniteComplex

abbrev Vertex (K : FiniteComplex) := Fin K.n

def Carrier (K : FiniteComplex) :=
  {x : K.Vertex → ℝ // (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
    ∃ s ∈ K.complex.faces, ∀ i, i ∉ s → x i = 0}

instance (K : FiniteComplex) : TopologicalSpace K.Carrier :=
  inferInstanceAs (TopologicalSpace (Subtype _))

def Edge (K : FiniteComplex) (a b : K.Vertex) : Prop :=
  {a, b} ∈ K.complex.faces

def EdgePath (K : FiniteComplex) : List K.Vertex → Prop
  | [] => False
  | [_] => True
  | a :: b :: t => K.Edge a b ∧ K.EdgePath (b :: t)

def Closed (K : FiniteComplex) (p : List K.Vertex) : Prop :=
  ∃ a t, p = a :: (t ++ [a]) ∨ p = [a]

/-- An elementary disk move. A noncollapsed triangular face costs one;
    a spur or a collapsed edge costs zero. Contexts are unchanged. -/
inductive DiskMove (K : FiniteComplex) : List K.Vertex → List K.Vertex → ℕ → Prop
  | stutter (l r) (a) :
      DiskMove K (l ++ [a, a] ++ r) (l ++ [a] ++ r) 0
  | spur (l r) (a b) (h : K.Edge a b) :
      DiskMove K (l ++ [a, b, a] ++ r) (l ++ [a] ++ r) 0
  | triangle (l r) (a b c) (h : {a, b, c} ∈ K.complex.faces)
      (hne : ({a, b, c} : Finset K.Vertex).card = 3) :
      DiskMove K (l ++ [a, b, c] ++ r) (l ++ [a, c] ++ r) 1

/-- A disk certificate obtained by elementary triangle attachments/removals,
    with spurs/collapses allowed. The index is the number of triangular faces. -/
inductive DiskHomotopy (K : FiniteComplex) : List K.Vertex → List K.Vertex → ℕ → Prop
  | refl (p) : DiskHomotopy K p p 0
  | move {p q n} : DiskMove K p q n → DiskHomotopy K p q n
  | symm {p q n} : DiskHomotopy K p q n → DiskHomotopy K q p n
  | trans {p q r m n} : DiskHomotopy K p q m → DiskHomotopy K q r n →
      DiskHomotopy K p r (m + n)

def Disk (K : FiniteComplex) (p : List K.Vertex) (faces : ℕ) : Prop :=
  ∃ a, K.DiskHomotopy p [a] faces

def LinearDiskFilling (K : FiniteComplex) (C : ℝ) : Prop :=
  ∀ p, K.EdgePath p → K.Closed p → (∃ a, K.Disk p a) →
    ∃ a, K.Disk p a ∧ (a : ℝ) ≤ C * (p.length - 1 : ℕ)

def Aspherical (K : FiniteComplex) (x : K.Carrier) : Prop :=
  ∀ n : ℕ, Subsingleton (HomotopyGroup.Pi (n + 2) K.Carrier x)

end FiniteComplex

/-- A constant-speed metric segment, parametrized on [0,1]. -/
def IsSegment {X : Type*} [MetricSpace X] (γ : ℝ → X) (x y : X) : Prop :=
  γ 0 = x ∧ γ 1 = y ∧
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    dist (γ s) (γ t) = |s - t| * dist x y

def IsGeodesic (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ, IsSegment γ x y

/-- The CN characterization of CAT(0), with whole metric segments. -/
def CATZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ, IsSegment γ x y ∧
    ∀ z : X, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist z (γ t) ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
        t * (1 - t) * dist x y ^ 2

/-- The hyperbolic-cosh midpoint characterization of CAT(-1). -/
def CATNegOne (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ, IsSegment γ x y ∧
    ∀ z : X, Real.cosh (dist z (γ (1 / 2))) ≤
      (Real.cosh (dist z x) + Real.cosh (dist z y)) /
        (2 * Real.cosh (dist x y / 2))

/-- A proper, cocompact isometric action of a discrete group. -/
structure GeometricAction (G X : Type*) [Group G] [MetricSpace X] where
  act : G →* (X ≃ᵢ X)
  proper : ∀ C : Set X, IsCompact C →
    {g : G | ∃ x ∈ C, act g x ∈ C}.Finite
  cocompact : ∃ C : Set X, IsCompact C ∧ ∀ x : X, ∃ g : G, ∃ y ∈ C, act g y = x

universe u

def NoGeometricCATZeroAction (G : Type*) [Group G] : Prop :=
  ∀ (X : Type u) (_ : MetricSpace X), Nonempty X → ProperSpace X → CompleteSpace X →
    CATZero X → IsEmpty (GeometricAction G X)

def WordLength {G : Type*} [Group G] (S : Finset G) (g : G) : ℕ :=
  sInf {n | ∃ w : List G, w.length = n ∧
    (∀ a ∈ w, a ∈ S ∨ a⁻¹ ∈ S) ∧ w.prod = g}

def WordDistance {G : Type*} [Group G] (S : Finset G) (g h : G) : ℝ :=
  WordLength S (g⁻¹ * h)

/-- Four-point word hyperbolicity, for some finite generating set. -/
def WordHyperbolic (G : Type*) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ a b c d : G,
      WordDistance S a c + WordDistance S b d ≤
        max (WordDistance S a b + WordDistance S c d)
          (WordDistance S a d + WordDistance S b c) + 2 * δ

/-- A metric on the given finite polyhedron, not on a different topology. -/
def CompatibleLocallyCATNegOne (K : FiniteComplex) : Prop :=
  ∃ m : MetricSpace K.Carrier,
    m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace K.Carrier) ∧
    (letI := m
     IsGeodesic K.Carrier ∧ ∀ x : K.Carrier, ∃ r : ℝ, 0 < r ∧
       CATNegOne (Metric.ball x r))

/-- A finite aspherical complex with hyperbolic fundamental group, no geometric CAT(0)
action, and no homotopy equivalent finite complex admitting a locally CAT(-1) metric. -/
def MainStatement : Prop :=
  ∃ K : FiniteComplex, ∃ x : K.Carrier, ∃ C : ℝ,
    ConnectedSpace K.Carrier ∧ K.Aspherical x ∧ 0 ≤ C ∧ K.LinearDiskFilling C ∧
    NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x) ∧
    WordHyperbolic (FundamentalGroup K.Carrier x) ∧
    ∀ L : FiniteComplex, Nonempty (K.Carrier ≃ₕ L.Carrier) →
      ¬ CompatibleLocallyCATNegOne L


def main_statement : Prop :=
  MainStatement.{u}

end HyperbolicObstruction


end
end
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.HyperbolicObstruction.main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/257.md: The formalized result constructs a finite connected aspherical complex with a linear disk-filling bound whose fundamental group is word-hyperbolic but admits no geometric action on a nonempty proper complete $\mathrm{CAT}(0)$ space. It also excludes locally $\mathrm{CAT}(-1)$ geodesic metrics on every finite complex homotopy equivalent to the witness. The stronger claims that the witness is two-dimensional and that those models admit no locally $\mathrm{CAT}(0)$ metric are not included. -/
