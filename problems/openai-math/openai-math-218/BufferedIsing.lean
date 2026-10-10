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

- problem_id: BufferedIsing
- collection: openai-math
- question_id: openai-math:218
- source: openai-math
- source_locator: lean/ComparatorChallenges/BufferedIsing.lean#OAI.BufferedIsing.finite_graph_comparison
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Weak finite-range square-symmetric even multispin perturbations of the square-lattice Ising model preserve critical bulk spin and energy limits; weak square-symmetric contour interactions also yield chordal SLE3 interface limits. With sufficiently weak iid bond disorder of any fixed bounded nondegenerate mean-zero law, critical spin interfaces converge to the same law in probability over environments. ([Lean](lean/docs/218.md)) We prove pointwise comparison and finite stopping-band approximation theorems for the critical nearest-neighbor Ising model on the square lattice. Arbitrary common pinned spins are allowed in the comparison: the likelihood ratio is controlled by a zero-field FK connection probability on the graph with those vertices deleted. For an interface exploration across a band of fixed positive width, finitely many regular signed barriers approximate every good conditional target law in total variation, uniformly over bounded observables and sufficiently fine meshes.
- notes: OpenAI math result family 218, Conformal universality for weakly interacting and random-bond Ising models -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/218.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.BufferedIsing.finite_graph_comparison
- source_theorem_count: 1
- source_solution_module: OAI.Probability.Ising.Main
- source_papers: preprints/Buffered-comparison-and-stopping-band-resolution-in-critical-Ising-September-23-2026/paper.pdf
- source_scope_note: lean/docs/218.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- A finite graph given by its edge list. Zero couplings can encode missing edges.
Edges are indexed separately so parallel edges are counted separately. -/
structure FiniteGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  coupling : Fin m → ℝ
  coupling_nonneg : ∀ e, 0 ≤ coupling e
  no_loops : ∀ e, left e ≠ right e

abbrev Spins (n : ℕ) := Fin n → Bool

def spin (b : Bool) : ℝ := if b then 1 else -1

noncomputable def energy {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : ℝ :=
  (∑ e, G.coupling e * spin (σ (G.left e)) * spin (σ (G.right e))) +
    ∑ v, h v * spin (σ v)

noncomputable def weight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : ℝ := Real.exp (energy G h σ)

def AgreesOn {n : ℕ} (S : Finset (Fin n)) (σ τ : Spins n) : Prop :=
  ∀ v ∈ S, σ v = τ v

noncomputable def constrainedSum {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (P : Spins n → Prop) : ℝ := by
  classical
  exact ∑ σ, if P σ then weight G h σ else 0

/-- Conditional probability of σ_I=a, with σ_J=b and σ_F=τ prescribed.
All sums are finite and all fields are finite real numbers. -/
noncomputable def conditionalProb {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (a b τ : Spins n) : ℝ :=
  constrainedSum G h (fun σ => AgreesOn I σ a ∧ AgreesOn J σ b ∧ AgreesOn F σ τ) /
    constrainedSum G h (fun σ => AgreesOn J σ b ∧ AgreesOn F σ τ)

/-- Edges remaining after DELETION, not pinning, of F. -/
def keptEdges {n m : ℕ} (G : FiniteGraph n m) (F : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun e => G.left e ∉ F ∧ G.right e ∉ F)

abbrev KeptVertex {n : ℕ} (F : Finset (Fin n)) := {v : Fin n // v ∉ F}

/-- Open-edge adjacency together with the two separate terminal identifications.
No virtual identification of common pins is present: those vertices are absent. -/
def comparisonRel {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (u v : KeptVertex F) : Prop :=
  (u.val ∈ I ∧ v.val ∈ I) ∨ (u.val ∈ J ∧ v.val ∈ J) ∨
    ∃ e ∈ ω, (G.left e = u.val ∧ G.right e = v.val) ∨
      (G.left e = v.val ∧ G.right e = u.val)

/-- The equivalence closure implements components of the contracted open graph. -/
def comparisonSetoid {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) : Setoid (KeptVertex F) :=
  Relation.EqvGen.setoid (comparisonRel G I J F ω)

noncomputable def clusterCount {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) : ℕ :=
  Nat.card (Quotient (comparisonSetoid G I J F ω))

/-- Zero-field FK weight with q=2 and p_e=1-exp(-2 K_e).
Parallel edges may be retained: the measure after summing them is the measure
for the summed parallel coupling. Loops created by contraction do not change
components and cancel from connection probabilities. -/
noncomputable def fkWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) : ℝ := by
  classical
  exact (2 : ℝ) ^ clusterCount G I J F ω *
    ∏ e ∈ keptEdges G F,
      if e ∈ ω then 1 - Real.exp (-2 * G.coupling e) else Real.exp (-2 * G.coupling e)

/-- Choose any i in I and j in J. The terminal connection is independent of
these choices because I and J are each identified. -/
noncomputable def qZero {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) : ℝ := by
  classical
  exact (∑ ω ∈ (keptEdges G F).powerset,
    if (comparisonSetoid G I J F ω).r i j then fkWeight G I J F ω else 0) /
    ∑ ω ∈ (keptEdges G F).powerset, fkWeight G I J F ω

/-- Any probability mixture of source prescriptions. Full configurations
index the mixture, but only their restrictions to J are used. Thus this is
exactly the class of all mixtures on {-1,+1}^J. -/
noncomputable def mixtureProb {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (a τ : Spins n)
    (mix : Spins n → ℝ) : ℝ :=
  ∑ b, mix b * conditionalProb G h I J F a b τ

/-- Finite-graph comparison for arbitrary probability mixtures on both sides.
Dirac mixtures recover the conditional laws. -/
def finite_graph_comparison_statement : Prop :=
  ∀ {n m : ℕ} (G : FiniteGraph n m) (h : Fin n → ℝ) (I J F : Finset (Fin n)) (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F) (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (a τ : Spins n) (mix mix' : Spins n → ℝ) (hmix : ∀ b, 0 ≤ mix b) (hmix' : ∀ b, 0 ≤ mix' b) (hmixsum : ∑ b, mix b = 1) (hmix'sum : ∑ b, mix' b = 1),
    Real.exp (-4 * Real.artanh (qZero G I J F i j)) ≤
        mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ∧
      mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ≤
        Real.exp (4 * Real.artanh (qZero G I J F i j))

end BufferedIsing

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.BufferedIsing.finite_graph_comparison_statement

end Problem

/- Formalization scope, from lean/docs/218.md: The formalized result compares conditional Ising probabilities on finite graphs when two boundary mixtures differ but a common set of spins is pinned. If $q_0$ is the associated zero-field Fortuin–Kasteleyn connection probability after deleting the pinned vertices, the likelihood ratio lies between $\exp(-4\mathrm{artanh}\,q_0)$ and $\exp(4\mathrm{artanh}\,q_0)$. The statement allows arbitrary external fields and arbitrary probability mixtures satisfying the stated disjointness conditions. The paper's finite stopping-band approximation theorem is outside this selected statement. -/
