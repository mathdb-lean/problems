import Mathlib.Data.Fintype.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

- problem_id: SecondKahnKalai
- collection: openai-math
- question_id: openai-math:176
- source: openai-math
- source_locator: lean/ComparatorChallenges/SecondKahnKalai.lean#OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the second Kahn–Kalai conjecture: for every finite simple graph H with h ≥ 1 edges and at most n vertices, its appearance threshold in $`G(n,p)`$ is at most $`C p_{\mathrm E}(n,H)(1+\log_2 h)`$, with universal C. Here $`p_{\mathrm E}`$ is the least density at which every subgraph of H has expected copy count at least 1/2. ([Lean](lean/docs/176.md)) We prove the second Kahn–Kalai conjecture. For every finite simple graph H with h ≥ 1 edges and at most n vertices, the threshold for $`G(n,p)`$ to contain an ordinary copy of H is at most $`C p_{\mathrm E}(n,H)(1+\log_2 h)`$, where C is universal. Here $`p_{\mathrm E}(n,H)`$ is the least density at which every subgraph of H has expected copy count at least one half.
- notes: OpenAI math result family 176, The second Kahn–Kalai conjecture with an edge-count bound -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/176.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.GraphThreshold.Main
- source_main_result: OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds
- source_papers: preprints/The-second-Kahn-Kalai-conjecture-September-24-2026/paper.pdf
- source_scope_note: lean/docs/176.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

universe u

namespace LeanBlast.SecondKahnKalai

def bernoulliWeight {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (W : Finset X) : ℝ :=
  ∏ x, if x ∈ W then p else 1 - p

def bernoulliExpectation {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (f : Finset X → ℝ) : ℝ :=
  ∑ W, bernoulliWeight p W * f W

def bernoulliProbability {X : Type u} [Fintype X] [DecidableEq X]
    (p : ℝ) (P : Finset X → Prop) : ℝ := by
  classical
  exact ∑ W, if P W then bernoulliWeight p W else 0

/-- The unordered non-loop edges of the complete graph on `n` vertices. -/
abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- A set of edges, interpreted as an ordinary graph on all `n` vertices. -/
def graphOfEdges {n : ℕ} (W : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Subtype.val '' (W : Set (Edge n)))

/-- The number of unordered edges, each counted once. -/
def edgeCount {V : Type u} (H : SimpleGraph V) : ℕ := Nat.card H.edgeSet

/-- Expected number of actual unlabelled non-induced copies in `G(n,p)`. -/
def expectedCopies {V : Type u} (n : ℕ) (p : ℝ) (H : SimpleGraph V) : ℝ :=
  bernoulliExpectation p (fun W : Finset (Edge n) =>
    ((graphOfEdges W).copyCount H : ℝ))

/-- Probability that `G(n,p)` contains at least one non-induced copy. -/
def containmentProbability {V : Type u} (n : ℕ) (p : ℝ)
    (H : SimpleGraph V) : ℝ :=
  bernoulliProbability p (fun W : Finset (Edge n) =>
    0 < (graphOfEdges W).copyCount H)

def criticalThreshold {V : Type u} (n : ℕ) (H : SimpleGraph V) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ (1 / 2 : ℝ) ≤ containmentProbability n p H}

def expectationThreshold {V : Type u} (n : ℕ) (H : SimpleGraph V) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧
    ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n p F.coe}

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def SecondKahnKalaiBounds {V : Type u} (n : ℕ) (H : SimpleGraph V) : Prop :=
  criticalThreshold n H ≤
      min 1 (2048 * Real.exp 50 * expectationThreshold n H *
        (1 + logTwo (edgeCount H : ℝ))) ∧
    criticalThreshold n H ≤
      6144 * Real.exp 50 * expectationThreshold n H * logTwo (n : ℝ)

def secondKahnKalaiBounds_statement : Prop :=
  ∀ (n : ℕ) (V : Type u) [Fintype V] (H : SimpleGraph V) (hn : 2 ≤ n) (hcard : Fintype.card V ≤ n) (hedge : 1 ≤ edgeCount H),
    SecondKahnKalaiBounds n H

end LeanBlast.SecondKahnKalai

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds_statement.{u}

end Problem

/- Formalization scope, from lean/docs/176.md: The second Kahn–Kalai conjecture compares the threshold for a random graph to contain a fixed graph with its expectation threshold. The formalized result proves the comparison up to a universal factor times $1+\log_2|E(H)|$, and hence up to a universal factor times $\log_2 n$, for every graph $H$ with at least one edge and at most $n$ vertices, $n\ge2$. The bounds use the actual containment and expectation thresholds. -/
