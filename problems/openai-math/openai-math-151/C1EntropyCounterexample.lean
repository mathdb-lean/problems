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

- problem_id: C1EntropyCounterexample
- collection: openai-math
- question_id: openai-math:151
- source: openai-math
- source_locator: lean/ComparatorChallenges/C1EntropyCounterexample.lean#OAI.Problem340.exists_C1_entropy_counterexample
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a noninvertible C1 self-map of a compact smooth manifold with zero topological entropy but eigenvalue 2 on second homology. This disproves the homological entropy lower bound for general C1 self-maps: homological growth need not force positive orbit complexity. ([Lean](lean/docs/151.md)) We disprove the general C1 self-map formulation of Shub's entropy conjecture. We construct a noninvertible C1 self-map of a compact smooth manifold without boundary whose topological entropy is zero, while its action on second real homology has eigenvalue 2. Thus the topological entropy is strictly smaller than the logarithm of the homological spectral radius.
- notes: OpenAI math result family 151, A <i>C</i><sup>1</sup> counterexample to the entropy conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/151.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem340.exists_C1_entropy_counterexample
- source_theorem_count: 1
- source_solution_module: OAI.Dynamics.EntropyCounterexample.Counterexample
- source_papers: preprints/A-C1-Counterexample-to-the-Entropy-Conjecture-September-25-2026/article.pdf
- source_scope_note: lean/docs/151.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

abbrev ClockAmbient := EuclideanSpace ℝ (Fin 2)

abbrev SphereAmbient := EuclideanSpace ℝ (Fin 3)

abbrev StandardClock := Metric.sphere (0 : ClockAmbient) (1 : ℝ)

abbrev StandardSphere2 := Metric.sphere (0 : SphereAmbient) (1 : ℝ)

abbrev CounterexampleManifold (q : ℕ) :=
  StandardClock × (Fin (q + 1) → StandardSphere2)

abbrev CounterexampleAmbient (q : ℕ) :=
  ClockAmbient × (Fin (q + 1) → SphereAmbient)

def standardEmbedding (q : ℕ) :
    CounterexampleManifold q → CounterexampleAmbient q :=
  fun x => (x.1.1, fun i => (x.2 i).1)

def IsC1SelfMap (q : ℕ) (f : CounterexampleManifold q → CounterexampleManifold q) : Prop :=
  Continuous f ∧
    ∀ x : CounterexampleManifold q,
      ∃ U : Set (CounterexampleAmbient q),
        IsOpen U ∧ standardEmbedding q x ∈ U ∧
          ∃ F : CounterexampleAmbient q → CounterexampleAmbient q,
            ContDiffOn ℝ 1 F U ∧
              ∀ y : CounterexampleManifold q,
                standardEmbedding q y ∈ U →
                  standardEmbedding q (f y) = F (standardEmbedding q y)

def continuousMapOf {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : ContinuousMap X Y :=
  ⟨f, hf⟩

abbrev RealSingularHomology (n : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)).obj (TopCat.of X))

def realHomologyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : X → Y) (hf : Continuous f) :
    RealSingularHomology n X →ₗ[ℝ] RealSingularHomology n Y :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)).map
      (TopCat.ofHom (continuousMapOf f hf))).hom

def totalRealHomologySpectralRadius {X : Type} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) : ℝ :=
  sSup {r : ℝ |
    ∃ n : ℕ, ∃ a b : ℝ,
      ∃ u v : RealSingularHomology n X,
        (u ≠ 0 ∨ v ≠ 0) ∧
        realHomologyMap n f hf u = a • u - b • v ∧
        realHomologyMap n f hf v = b • u + a • v ∧
        r = Real.sqrt (a ^ 2 + b ^ 2)}

def exists_C1_entropy_counterexample_statement : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q, ∃ hf : IsC1SelfMap q f, Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧ (∃ v : RealSingularHomology 2 (CounterexampleManifold q), v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧ 0 < Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧ ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3

end Problem340

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem340.exists_C1_entropy_counterexample_statement

end Problem

/- Formalization scope, from lean/docs/151.md: Shub's entropy conjecture predicts that a smooth self-map's topological entropy is at least the logarithm of the spectral radius of its action on real homology. The formalization gives a counterexample to the general $C^1$ self-map version: a noninvertible $C^1$ map on a compact smooth manifold without boundary has topological entropy zero, while its action on second real homology has a nonzero eigenvector with eigenvalue $2$. Thus the homological lower bound is strictly positive and fails for this map. -/
