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

- problem_id: CannonGeometricAction
- collection: openai-math
- question_id: openai-math:246
- source: openai-math
- source_locator: lean/ComparatorChallenges/CannonGeometricAction.lean#OAI.CannonRelease.cannon
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Every word-hyperbolic group with boundary homeomorphic to S2 admits a proper cocompact isometric action on hyperbolic three-space with finite kernel, proving Cannon's conjecture. Every torsion-free such group is therefore the fundamental group of a closed hyperbolic three-manifold. ([Lean](lean/docs/246.md)) We prove that every hyperbolic group whose boundary is homeomorphic to the two-sphere admits a proper cocompact isometric action on hyperbolic three-space with finite kernel. This resolves Cannon's conjecture positively.
- notes: OpenAI math result family 246, Cannon's conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/246.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CannonRelease.cannon
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.Cannon.Main
- source_papers: preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/246.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
namespace CannonRelease

universe u

structure CayleyData (G : Type u) [Group G] where
  generators : Finset G
  symmetric : ∀ x ∈ generators, x⁻¹ ∈ generators
  connected : (SimpleGraph.mulCayley (generators : Set G)).Connected

def CayleyData.graph {G : Type u} [Group G] (D : CayleyData G) : SimpleGraph G :=
  SimpleGraph.mulCayley (D.generators : Set G)

/-- A uniform thinness constant for geodesic triangles in the Cayley graph. -/
def CayleyData.ThinTriangles {G : Type u} [Group G] (D : CayleyData G) : Prop :=
  ∃ δ : ℕ, ∀ x y z : G,
    ∀ p : D.graph.Walk x y, ∀ q : D.graph.Walk y z, ∀ r : D.graph.Walk z x,
      p.length = D.graph.dist x y → q.length = D.graph.dist y z →
      r.length = D.graph.dist z x →
      ∀ a ∈ p.support, ∃ b ∈ q.support ++ r.support, D.graph.dist a b ≤ δ

/-- Based geodesic rays, parametrized at integer times. -/
def BasedRay {G : Type u} [Group G] (D : CayleyData G) :=
  {r : ℕ → G // r 0 = 1 ∧ ∀ i j, D.graph.dist (r i) (r j) = Nat.dist i j}

instance {G : Type u} [Group G] [TopologicalSpace G] (D : CayleyData G) :
    TopologicalSpace (BasedRay D) := inferInstanceAs (TopologicalSpace {r : ℕ → G //
      r 0 = 1 ∧ ∀ i j, D.graph.dist (r i) (r j) = Nat.dist i j})

/-- Finite synchronous distance, equivalent to asymptoticity for based rays. -/
def raySetoid {G : Type u} [Group G] (D : CayleyData G) : Setoid (BasedRay D) where
  r r s := ∃ C : ℕ, ∀ n, D.graph.dist (r.val n) (s.val n) ≤ C
  iseqv := by
    constructor
    · intro r
      exact ⟨0, fun n => by simp⟩
    · rintro r s ⟨C, hC⟩
      exact ⟨C, fun n => by rw [SimpleGraph.dist_comm]; exact hC n⟩
    · rintro r s t ⟨C, hC⟩ ⟨E, hE⟩
      refine ⟨C + E, fun n => ?_⟩
      exact le_trans ((D.connected (r.val n) (s.val n)).dist_triangle_left (t.val n))
        (Nat.add_le_add (hC n) (hE n))

def Boundary {G : Type u} [Group G] (D : CayleyData G) := Quotient (raySetoid D)

instance {G : Type u} [Group G] [TopologicalSpace G] (D : CayleyData G) :
    TopologicalSpace (Boundary D) :=
  inferInstanceAs (TopologicalSpace (Quotient (raySetoid D)))

abbrev SphereTwo := {x : EuclideanSpace ℝ (Fin 3) // x ∈ Metric.sphere 0 1}

/-- The upper-half-space model of hyperbolic three-space. -/
def HyperbolicThree := {x : Fin 3 → ℝ // 0 < x 2}

instance : TopologicalSpace HyperbolicThree :=
  inferInstanceAs (TopologicalSpace {x : Fin 3 → ℝ // 0 < x 2})

def hyperbolicDist (x y : HyperbolicThree) : ℝ :=
  Real.arcosh (1 + (∑ i : Fin 3, (x.val i - y.val i) ^ 2) / (2 * x.val 2 * y.val 2))

/-- The full isometry group, including orientation-reversing isometries. -/
def hyperbolicIsometries : Subgroup (HyperbolicThree ≃ₜ HyperbolicThree) where
  carrier := {f | ∀ x y, hyperbolicDist (f x) (f y) = hyperbolicDist x y}
  one_mem' := by
    change ∀ x y, hyperbolicDist x y = hyperbolicDist x y
    intros
    rfl
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    simpa using (hf (f.symm x) (f.symm y)).symm

abbrev H3Isom := ↥hyperbolicIsometries

def ProperAction {G : Type u} [Group G] (ρ : G →* H3Isom) : Prop :=
  ∀ K : Set HyperbolicThree, IsCompact K →
    {g : G | ∃ x ∈ K, (ρ g).val x ∈ K}.Finite

def CocompactAction {G : Type u} [Group G] (ρ : G →* H3Isom) : Prop :=
  ∃ K : Set HyperbolicThree, IsCompact K ∧
    ∀ x : HyperbolicThree, ∃ g : G, ∃ y ∈ K, (ρ g).val y = x

def cannon_statement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G] (D : CayleyData G) (hthin : D.ThinTriangles) (hsphere : Nonempty (Boundary D ≃ₜ SphereTwo)),
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧
      (ρ.ker : Set G).Finite

end CannonRelease
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.CannonRelease.cannon_statement.{u}

end Problem

/- Formalization scope, from lean/docs/246.md: Cannon's conjecture asks whether a hyperbolic group with boundary homeomorphic to the two-sphere acts geometrically on hyperbolic three-space. The formalization proves that such a group admits an isometric action on $\mathbb H^3$ that is proper and cocompact and has finite kernel. Hyperbolicity is expressed through uniformly thin geodesic triangles in a Cayley graph, and the boundary hypothesis is a homeomorphism with $S^2$. -/
