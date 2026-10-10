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

- problem_id: FreeUniformSpanningForest
- collection: openai-math
- question_id: openai-math:231
- source: openai-math
- source_locator: lean/ComparatorChallenges/FreeUniformSpanningForest.lean#OAI.Problem336.fusf_is_factor_iid
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: On every infinite connected locally finite simple unweighted graph, the free uniform spanning forest is a factor of independent vertex labels, by one isomorphism-equivariant rule using no root. Translation-invariant strongly Rayleigh binary processes on every countable group, including invariant determinantal processes with Hermitian positive-contraction kernels, are also factors of IID. ([Lean](lean/docs/231.md)) We prove that the free uniform spanning forest is a factor of IID on every infinite connected locally finite simple unweighted graph. One Borel rule works for all such graphs and uses no root, answering affirmatively the general factor question for unimodular random graphs. We also show that every translation-invariant strongly Rayleigh process indexed by a countable group is a factor of IID, including invariant determinantal processes with Hermitian positive-contraction kernels. This group-action conclusion requires no amenability.
- notes: OpenAI math result family 231, The free uniform spanning forest is a factor of IID -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/231.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem336.fusf_is_factor_iid
- source_theorem_count: 1
- source_solution_module: OAI.Probability.SpanningForest.Factor
- source_papers: preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf
- source_scope_note: lean/docs/231.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem336

abbrev GraphCode :=
  {a : ℕ → ℕ → Bool //
    (∀ u, a u u = false) ∧ (∀ u v, a u v = a v u)}

abbrev EdgeCode := {p : ℕ × ℕ // p.1 < p.2}

abbrev EdgeConfiguration := EdgeCode → Bool

abbrev FactorRule := GraphCode → (ℕ → ℝ) → EdgeCode → Bool

abbrev FiniteSubgraphCode := Finset ℕ × Finset (ℕ × ℕ)

def Adj (G : GraphCode) (u v : ℕ) : Prop := G.1 u v = true

def GraphConnected (G : GraphCode) : Prop :=
  ∀ u v, Relation.ReflTransGen (fun x y => Adj G x y) u v

def GraphLocallyFinite (G : GraphCode) : Prop :=
  ∀ u, Set.Finite {v : ℕ | Adj G u v}

def mkEdge (u v : ℕ) (h : u ≠ v) : EdgeCode := by
  by_cases huv : u < v
  · exact ⟨(u, v), huv⟩
  · exact ⟨(v, u), lt_of_le_of_ne (Nat.le_of_not_gt huv) (Ne.symm h)⟩

def rawPair (u v : ℕ) : ℕ × ℕ :=
  if u < v then (u, v) else (v, u)

def relabelGraph (σ : Equiv ℕ ℕ) (G : GraphCode) : GraphCode :=
  ⟨fun u v => G.1 (σ.symm u) (σ.symm v), by
    constructor
    · intro u
      exact G.2.1 (σ.symm u)
    · intro u v
      exact G.2.2 (σ.symm u) (σ.symm v)⟩

def relabelLabels (σ : Equiv ℕ ℕ) (U : ℕ → ℝ) : ℕ → ℝ :=
  fun u => U (σ.symm u)

def mapEdge (σ : Equiv ℕ ℕ) (e : EdgeCode) : EdgeCode :=
  mkEdge (σ e.1.1) (σ e.1.2) (by
    intro h
    apply Nat.ne_of_lt e.2
    exact σ.injective h)

def RuleBorel (Phi : FactorRule) : Prop :=
  Measurable
    (fun q : GraphCode × ((ℕ → ℝ) × EdgeCode) =>
      Phi q.1 q.2.1 q.2.2)

def RuleEquivariant (Phi : FactorRule) : Prop :=
  ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode),
    Phi (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) =
      Phi G U e

def TreeAdj (T : Finset (ℕ × ℕ)) (u v : ℕ) : Prop :=
  rawPair u v ∈ T

def SubgraphAdj (K : FiniteSubgraphCode) (u v : ℕ) : Prop :=
  u ∈ K.1 ∧ v ∈ K.1 ∧ rawPair u v ∈ K.2

def TreeOn (K : FiniteSubgraphCode)
    (T : Finset (ℕ × ℕ)) : Prop :=
  T ⊆ K.2 ∧
  T.card + 1 = K.1.card ∧
  ∀ u ∈ K.1, ∀ v ∈ K.1,
    Relation.ReflTransGen (TreeAdj T) u v

def spanningTrees (K : FiniteSubgraphCode) :
    Finset (Finset (ℕ × ℕ)) := by
  classical
  exact K.2.powerset.filter (TreeOn K)

def ustCylinder (K : FiniteSubgraphCode)
    (A B : Finset EdgeCode) : ℝ≥0∞ := by
  classical
  let all := spanningTrees K
  let good := all.filter (fun T =>
    (∀ e ∈ A, e.1 ∈ T) ∧ (∀ e ∈ B, e.1 ∉ T))
  exact (good.card : ℝ≥0∞) / (all.card : ℝ≥0∞)

def IsFiniteConnectedSubgraph
    (G : GraphCode) (K : FiniteSubgraphCode) : Prop :=
  K.1.Nonempty ∧
  (∀ p ∈ K.2,
    p.1 ∈ K.1 ∧ p.2 ∈ K.1 ∧ p.1 < p.2 ∧ Adj G p.1 p.2) ∧
  ∀ u ∈ K.1, ∀ v ∈ K.1,
    Relation.ReflTransGen (SubgraphAdj K) u v

def IsConnectedExhaustion
    (G : GraphCode) (H : ℕ → FiniteSubgraphCode) : Prop :=
  (∀ n, IsFiniteConnectedSubgraph G (H n)) ∧
  (∀ n, (H n).1 ⊆ (H (n + 1)).1 ∧
    (H n).2 ⊆ (H (n + 1)).2) ∧
  (∀ u v, u < v → Adj G u v →
    ∃ n, (u, v) ∈ (H n).2)

def uniform01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def IsVertexIID {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (U : ℕ → Ω → ℝ) : Prop :=
  (∀ i, Measurable (U i)) ∧
  ∀ (s : Finset ℕ) (A : ℕ → Set ℝ),
    (∀ i ∈ s, MeasurableSet (A i)) →
    P {ω | ∀ i ∈ s, U i ω ∈ A i} =
      Finset.prod s (fun i => uniform01 (A i))

def HasFUSFLaw {Ω : Type} [MeasurableSpace Ω]
    (G : GraphCode) (P : Measure Ω)
    (X : Ω → EdgeConfiguration) : Prop :=
  (∀ e, Measurable (fun ω => X ω e)) ∧
  ∀ (H : ℕ → FiniteSubgraphCode), IsConnectedExhaustion G H →
    ∀ (A B : Finset EdgeCode),
      Filter.Tendsto
        (fun n => ustCylinder (H n) A B)
        Filter.atTop
        (nhds (P {ω |
          (∀ e ∈ A, X ω e = true) ∧
          (∀ e ∈ B, X ω e = false)}))

def WorksOnGraph (Phi : FactorRule) (G : GraphCode) : Prop :=
  GraphConnected G → GraphLocallyFinite G →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (U : ℕ → Ω → ℝ),
    IsVertexIID P U →
    HasFUSFLaw G P
      (fun ω e => Phi G (fun v => U v ω) e)

def fusf_is_factor_iid_statement : Prop :=
  ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧ ∀ G : GraphCode, WorksOnGraph Phi G

end Problem336

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem336.fusf_is_factor_iid_statement

end Problem

/- Formalization scope, from lean/docs/231.md: The formalization proves that the free uniform spanning forest is a factor of independent identically distributed vertex labels on every infinite connected locally finite simple unweighted graph. One Borel equivariant rule works for all such graphs and uses no distinguished root. The linked supplements also give equivariant IID sampling for invariant strongly Rayleigh laws on countable groups and existence, uniqueness, and IID-factor results for determinantal laws with Hermitian positive-contraction kernels on countable index sets. These group results require neither amenability nor finite generation, and the kernels need not be trace class. -/
