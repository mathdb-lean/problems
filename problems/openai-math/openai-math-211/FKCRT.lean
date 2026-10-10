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

- problem_id: FKCRT
- collection: openai-math
- question_id: openai-math:211
- source: openai-math
- source_locator: lean/ComparatorChallenges/FKCRT.lean#OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Critical Fortuin–Kasteleyn planar maps converge to Liouville quantum gravity spheres for $`0\lt q\le4`$ and to the Brownian continuum random tree for q &gt; 4, establishing the surface-to-tree geometric transition. For FK–Ising and spanning-tree-weighted maps, stationary random walks converge to Liouville Brownian motion on the limiting sphere. The FK–Ising spectral result also gives convergence of eigenvalues and heat traces, using the stated Brownian/LQG inputs. ([Lean](lean/docs/211.md)) We prove the finite-volume continuum-random-tree prediction for critical Fortuin–Kasteleyn planar maps at every fixed q &gt; 4. After rescaling graph distances by a constant times n−1/2, an n-edge map with normalized degree measure converges to the Brownian continuum random tree in the Gromov–Hausdorff–Prokhorov topology. The convergence holds through all positive integer sizes.
- notes: OpenAI math result family 211, The geometric phase diagram, diffusion, and spectra of random planar maps -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/211.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt
- source_theorem_count: 1
- source_solution_module: OAI.Probability.FKMaps.Convergence
- source_papers: preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf
- source_scope_note: lean/docs/211.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
Finite Fortuin–Kasteleyn maps and the Brownian continuum random tree.

All combinatorial maps below have a distinguished dart 0 and are quotiented
by orientation-preserving dart relabellings fixing that dart. A rotation system
with Euler characteristic 2 encodes precisely a connected oriented-sphere map.
No simplicity restriction is imposed. Vertices and edges are rotation and
edge-reversal orbits, respectively. Every edge subset is included in the law.
The index n here represents source size n+1, so the limit is through ALL
positive edge sizes, not a subsequence.

MetricMeasureData packages the actual distance, measurable space and measure,
without using arbitrary representatives of measure-preserving isometry classes
as a global typeclass. Valid objects are compact metric probability spaces.
The GHP extended distance is the infimum over common isometric embeddings,
represented by pseudometrics on the disjoint union; zero cross distances simply
identify points in the common ambient space. Tests are bounded functions
continuous for that distance on valid objects. Thus GHP convergence is written
in its bounded-continuous-test (weak distributional convergence) definition.

A standard normalized Brownian excursion is represented in its standard
three-dimensional Bessel-bridge realization: the norm of three independent
standard Brownian bridges of duration 1. No rescaling of the excursion is used.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal

namespace FKCRT

abbrev Dart (n : ℕ) := Fin (2 * (n + 1))

abbrev Orbit {n : ℕ} (s : Equiv.Perm (Dart n)) :=
  Quotient (Equiv.Perm.SameCycle.setoid s)

def orbit {n : ℕ} (s : Equiv.Perm (Dart n)) (d : Dart n) : Orbit s :=
  Quotient.mk _ d

instance {n : ℕ} (s : Equiv.Perm (Dart n)) : Fintype (Orbit s) := Fintype.ofFinite _

/-- The spanning graph with precisely the edges in A, with loops omitted only
from adjacency: they still exist as edge orbits, have FK weight, and contribute
two darts to the degree measure. Omitting loops does not change distance or k. -/
def spanningGraph {n : ℕ} (a s : Equiv.Perm (Dart n)) (A : Set (Orbit a)) :
    SimpleGraph (Orbit s) :=
  SimpleGraph.fromRel fun v w =>
    ∃ d : Dart n, orbit a d ∈ A ∧ orbit s d = v ∧ orbit s (a d) = w

/-- Labelled connected orientable genus-zero rotation systems. -/
def MapConditions {n : ℕ} (P : Equiv.Perm (Dart n) × Equiv.Perm (Dart n)) : Prop :=
  Function.Involutive P.1 ∧ (∀ d, P.1 d ≠ d) ∧
  (spanningGraph P.1 P.2 Set.univ).Connected ∧
  Nat.card (Orbit P.2) + Nat.card (Orbit (P.2 * P.1)) = n + 3

abbrev LabelledMap (n : ℕ) :=
  {P : Equiv.Perm (Dart n) × Equiv.Perm (Dart n) // MapConditions P}

/-- Root-preserving isomorphism of oriented maps (both dart permutations intertwine). -/
def MapIso {n : ℕ} (M N : LabelledMap n) : Prop :=
  ∃ r : Equiv.Perm (Dart n), r 0 = 0 ∧
    (∀ d, N.val.1 (r d) = r (M.val.1 d)) ∧
    (∀ d, N.val.2 (r d) = r (M.val.2 d))

abbrev RootedMap (n : ℕ) := Quotient (Relation.EqvGen.setoid (@MapIso n))

instance (n : ℕ) : Fintype (RootedMap n) := Fintype.ofFinite _

def reversal {n : ℕ} (M : RootedMap n) : Equiv.Perm (Dart n) := M.out.val.1

def rotation {n : ℕ} (M : RootedMap n) : Equiv.Perm (Dart n) := M.out.val.2

abbrev Vertex {n : ℕ} (M : RootedMap n) := Orbit (rotation M)
abbrev Edge {n : ℕ} (M : RootedMap n) := Orbit (reversal M)

def graph {n : ℕ} (M : RootedMap n) (A : Set (Edge M)) : SimpleGraph (Vertex M) :=
  spanningGraph (reversal M) (rotation M) A

/-- The source k_M(A), including isolated vertices. -/
def clusterCount {n : ℕ} (M : RootedMap n) (A : Finset (Edge M)) : ℕ :=
  Nat.card (graph M (A : Set (Edge M))).ConnectedComponent

/-- Exact decorated finite-map weight from eq:finite-law. -/
def fkWeight {n : ℕ} (q : ℝ) (M : RootedMap n) (A : Finset (Edge M)) : ℝ :=
  Real.rpow q ((clusterCount M A : ℝ) +
    ((A.card : ℝ) - (Nat.card (Vertex M) : ℝ)) / 2)

def partition (q : ℝ) (n : ℕ) : ℝ :=
  ∑ M : RootedMap n, ∑ A : Finset (Edge M), fkWeight q M A

/-- Unbundled presentation of a measured metric space; validity is specified below. -/
structure MetricMeasureData where
  Carrier : Type
  distance : Carrier → Carrier → ℝ
  measurableSpace : MeasurableSpace Carrier
  mass : @Measure Carrier measurableSpace

/-- Exactly compact metric probability spaces, with their Borel sigma algebras. -/
def MetricMeasureData.Valid (X : MetricMeasureData) : Prop :=
  ∃ m : MetricSpace X.Carrier,
    letI := m
    (∀ x y, dist x y = X.distance x y) ∧
    CompactSpace X.Carrier ∧ X.measurableSpace = borel X.Carrier ∧
    X.mass Set.univ = 1

/-- Normalized degree measure is uniform dart mass pushed to vertices. -/
def degreeMass {n : ℕ} (M : RootedMap n) :
    @Measure (Vertex M) ⊤ :=
  letI : MeasurableSpace (Vertex M) := ⊤
  ∑ d : Dart n, ENNReal.ofReal (1 / (2 * (n + 1) : ℝ)) •
    Measure.dirac (orbit (rotation M) d)

/-- Root and decoration are not included in the metric probability space. -/
def mapSpace {n : ℕ} (scale : ℝ) (M : RootedMap n) : MetricMeasureData where
  Carrier := Vertex M
  distance v w := scale * ((graph M Set.univ).dist v w : ℝ)
  measurableSpace := ⊤
  mass := degreeMass M

/-- An ambient pseudometric on the disjoint union giving isometric embeddings. -/
def Amalgamates (X Y : MetricMeasureData)
    (m : PseudoMetricSpace (X.Carrier ⊕ Y.Carrier)) : Prop :=
  letI := m
  (∀ x x', dist (Sum.inl x : X.Carrier ⊕ Y.Carrier) (Sum.inl x') = X.distance x x') ∧
  (∀ y y', dist (Sum.inr y : X.Carrier ⊕ Y.Carrier) (Sum.inr y') = Y.distance y y')

def ambientCost (X Y : MetricMeasureData)
    (m : PseudoMetricSpace (X.Carrier ⊕ Y.Carrier)) : ℝ≥0∞ :=
  letI := m
  letI : MeasurableSpace (X.Carrier ⊕ Y.Carrier) := borel _
  max (Metric.hausdorffEDist (Set.range (Sum.inl : X.Carrier → X.Carrier ⊕ Y.Carrier))
    (Set.range (Sum.inr : Y.Carrier → X.Carrier ⊕ Y.Carrier)))
    (levyProkhorovEDist
      (@Measure.map X.Carrier (X.Carrier ⊕ Y.Carrier) X.measurableSpace
        (borel _) Sum.inl X.mass)
      (@Measure.map Y.Carrier (X.Carrier ⊕ Y.Carrier) Y.measurableSpace
        (borel _) Sum.inr Y.mass))

/-- The common-isometric-embedding definition of the source GHP distance. -/
def ghpEDist (X Y : MetricMeasureData) : ℝ≥0∞ :=
  ⨅ m : {m : PseudoMetricSpace (X.Carrier ⊕ Y.Carrier) // Amalgamates X Y m},
    ambientCost X Y m.val

/-- Bounded continuous tests on compact metric probability spaces modulo
measure-preserving isometry, expressed on presentations. -/
def IsGHPTest (F : MetricMeasureData → ℝ) : Prop :=
  (∃ C : ℝ, ∀ X, |F X| ≤ C) ∧
  ∀ X, X.Valid → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ Y, Y.Valid → ghpEDist X Y < ENNReal.ofReal δ → |F Y - F X| < ε

/-- Source excursion pseudometric, with the closed interval minimum. -/
def excursionDist (e : unitInterval → ℝ) (s t : unitInterval) : ℝ :=
  e s + e t - 2 * sInf (e '' Set.uIcc s t)

abbrev ExcursionTree (e : unitInterval → ℝ) :=
  Quotient (Relation.EqvGen.setoid (fun s t => excursionDist e s t = 0))

def treeProjection (e : unitInterval → ℝ) (t : unitInterval) : ExcursionTree e :=
  Quotient.mk _ t

/-- The quotient by d_e=0, its induced metric, and pushforward of uniform time.
The equivalence closure is redundant for continuous e; the induced distance
is independent of representatives, as required by the pseudometric proof. -/
def treeSpace (e : unitInterval → ℝ) : MetricMeasureData :=
  letI : TopologicalSpace (ExcursionTree e) :=
    TopologicalSpace.coinduced (treeProjection e) inferInstance
  letI : MeasurableSpace (ExcursionTree e) := borel _
  { Carrier := ExcursionTree e
    distance := fun x y => excursionDist e x.out y.out
    measurableSpace := borel _
    mass := Measure.map (treeProjection e) (volume : Measure unitInterval) }

/-- Standard normalized excursion, realized as the 3D Bessel bridge. -/
def standardExcursion {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (ω : Ω)
    (t : unitInterval) : ℝ :=
  Real.sqrt (∑ i : Fin 3, (B i ⟨(t : ℝ), t.property.1⟩ ω -
    (t : ℝ) * B i 1 ω) ^ 2)

/-- Exact expectation under the finite law, with n+1 edges. -/
def finiteExpectation (q scale : ℝ) (n : ℕ) (F : MetricMeasureData → ℝ) : ℝ :=
  ∑ M : RootedMap n, ∑ A : Finset (Edge M),
    (fkWeight q M A / partition q n) * F (mapSpace scale M)

def brownianExpectation {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Fin 3 → ℝ≥0 → Ω → ℝ) (F : MetricMeasureData → ℝ) : ℝ :=
  ∫ ω, F (treeSpace (standardExcursion B ω)) ∂P

/-- thm:main. The quantifiers over Brownian realizations express that the limit
is the standard excursion-tree law, not a coupling-specific object. -/
def MainStatement : Prop :=
  ∀ q : ℝ, 4 < q → ∃ c : ℝ, 0 < c ∧
    ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ),
      @IsProbabilityMeasure Ω mΩ P →
      ∀ B : Fin 3 → ℝ≥0 → Ω → ℝ,
        (∀ i, @IsBrownianReal Ω mΩ (B i) P) →
        @iIndepFun Ω (Fin 3) mΩ (fun _ => ℝ≥0 → ℝ) (fun _ => inferInstance)
          (fun i ω t => B i t ω) P →
        ∀ F : MetricMeasureData → ℝ, IsGHPTest F →
          Tendsto (fun n : ℕ => finiteExpectation q (c / Real.sqrt (n + 1)) n F)
            atTop (𝓝 (@brownianExpectation Ω mΩ P B F))


/-- Finite FK maps converge in GHP distribution to the standard Brownian CRT. -/
def finite_fk_maps_converge_to_brownian_crt_statement : Prop :=
  MainStatement

end FKCRT
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt_statement

end Problem

/- Formalization scope, from lean/docs/211.md: For every fixed $q>4$, the formalization proves the Brownian continuum-random-tree limit for critical finite Fortuin–Kasteleyn planar maps. After rescaling graph distances in an $n$-edge map by a constant depending on $q$ times $n^{-1/2}$ and using normalized degree measure, the metric-measure space converges in distribution to the Brownian continuum random tree in the Gromov–Hausdorff–Prokhorov topology. The convergence holds through all positive integer sizes. -/
