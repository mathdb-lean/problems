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

- problem_id: MatchingEntropyBounds
- collection: openai-math
- question_id: openai-math:113
- source: openai-math
- source_locator: lean/ComparatorChallenges/MatchingEntropyBounds.lean#OAI.MatchingEntropyBounds.Refined.pointwise_entropy
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives a fully polynomial randomized approximation scheme for counting perfect matchings in arbitrary finite simple graphs, with exact detection of zero counts. Also proves the perfect-matching entropy conjecture of Anari, Oveis Gharan, and Vinzant, bounding the maximum entropy of a matching law at every feasible edge-marginal vector in a loopless labelled multigraph, including boundary points. ([Lean](lean/docs/113.md)) We give a fully polynomial randomized approximation scheme (FPRAS) for counting perfect matchings in arbitrary finite simple undirected graphs, resolving the general-graph perfect-matching approximation problem. The algorithm returns zero with certainty when no perfect matching exists. Otherwise, it achieves relative error ε with failure probability at most δ in worst-case bit time polynomial in the input length, $`\varepsilon ^{-1}`$, and $`\log\delta^{-1}`$. We prove the perfect-matching entropy conjecture of Anari, Oveis Gharan, and Vinzant. For every feasible vector x of perfect-matching edge marginals in a loopless labelled multigraph on $`2m\ge2`$ vertices, the maximum entropy $`H(x)`$ of a matching law with marginals x satisfies
- notes: OpenAI math result family 113, Approximate counting and entropy of perfect matchings -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/113.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.MatchingEntropyBounds.Refined.pointwise_entropy
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.MatchingEntropy.Main
- source_papers: preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf preprints/Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026/main.pdf
- source_scope_note: lean/docs/113.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uIndex uι

namespace MatchingEntropyBounds

structure LooplessGraph (V : Type uV) (E : Type uE) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

variable {V : Type uV} {E : Type uE}
  [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def Incident (G : LooplessGraph V E) (v : V) (e : E) : Prop :=
  G.left e = v ∨ G.right e = v

instance incidentDecidable (G : LooplessGraph V E) (v : V) (e : E) :
    Decidable (G.Incident v e) := inferInstanceAs (Decidable (G.left e = v ∨ G.right e = v))

def IsPerfectMatching (G : LooplessGraph V E) (M : Finset E) : Prop :=
  ∀ v, ∃! e, e ∈ M ∧ G.Incident v e

abbrev Matching (G : LooplessGraph V E) := {M : Finset E // G.IsPerfectMatching M}

instance matchingFintype (G : LooplessGraph V E) : Fintype G.Matching :=
  Fintype.ofFinite _

def indicator (G : LooplessGraph V E) (M : G.Matching) (e : E) : ℝ :=
  if e ∈ M.val then 1 else 0

def polytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  convexHull ℝ (Set.range G.indicator)

def mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (e : E) : ℝ :=
  ∑ M, p M * G.indicator M e

end LooplessGraph

def probabilitySimplex (Index : Type uIndex) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

def LooplessGraph.feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) : Set (G.Matching → ℝ) :=
  {p | p ∈ probabilitySimplex G.Matching ∧ G.mean p = y}

def entropy {ι : Type uι} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

def maxMatchingEntropy (G : LooplessGraph V E) (y : E → ℝ) : ℝ :=
  sSup (entropy '' G.feasibleLaws y)

namespace Refined

def complementEntropy (x : E → ℝ) : ℝ := entropy (fun e => 1 - x e)

end Refined

open Module Matrix

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open LooplessGraph

def Refined.pointwise_entropy_statement : Prop :=
  ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (m : ℕ) (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching) (x : E → ℝ) (hx : x ∈ G.polytope),
    entropy x - (2 - 2 / (m : ℝ)) * complementEntropy x ≤ maxMatchingEntropy G x ∧
      maxMatchingEntropy G x ≤ entropy x

end MatchingEntropyBounds

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{uV, uE} : Prop :=
  _root_.OAI.MatchingEntropyBounds.Refined.pointwise_entropy_statement.{uV, uE}

end Problem

/- Formalization scope, from lean/docs/113.md: The formalization gives a fully polynomial randomized approximation scheme for counting perfect matchings in every finite simple undirected graph. For rational $0<\varepsilon<1$ and $0<\delta<1/2$, it returns a nonnegative rational estimate with relative error at most $\varepsilon$ with probability at least $1-\delta$. If the graph has no perfect matching, every execution returns zero. The algorithm is a fixed finite-alphabet randomized machine. Its worst-case running time is polynomial in the binary input length, $\varepsilon^{-1}$, and $\log(\delta^{-1})$, including on unsuccessful random tapes. For feasible edge marginals $x$ of perfect matchings in a loopless multigraph on $2m$ vertices, let $F(x)=-\sum_e x_e\log x_e$, $B(x)=-\sum_e(1-x_e)\log(1-x_e)$, and let $H(x)$ be the maximum entropy of a matching law with those marginals. The formalization proves $F(x)-(2-2/m)B(x)\le H(x)\le F(x)$ for $m\ge1$, including boundary points of the polytope. It retains the earlier coefficient-eight entropy bound and the deterministic counting approximations with factors $512^n$ for loopless graphs and $2^{18n}$ with singleton loops. A further statement identifies the exact face obtained by expanding a degree-three vertex into a triangle and shows that minimal faces are carried to minimal faces by the expansion. The paper's sharp global face-dimension bound is not part of that selected statement. -/
