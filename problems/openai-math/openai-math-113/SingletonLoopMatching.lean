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

- problem_id: SingletonLoopMatching
- collection: openai-math
- question_id: openai-math:113
- source: openai-math
- source_locator: lean/ComparatorChallenges/SingletonLoopMatching.lean#OAI.LoopMatching.fullEndpoint
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives a fully polynomial randomized approximation scheme for counting perfect matchings in arbitrary finite simple graphs, with exact detection of zero counts. Also proves the perfect-matching entropy conjecture of Anari, Oveis Gharan, and Vinzant, bounding the maximum entropy of a matching law at every feasible edge-marginal vector in a loopless labelled multigraph, including boundary points. ([Lean](lean/docs/113.md)) We give a fully polynomial randomized approximation scheme (FPRAS) for counting perfect matchings in arbitrary finite simple undirected graphs, resolving the general-graph perfect-matching approximation problem. The algorithm returns zero with certainty when no perfect matching exists. Otherwise, it achieves relative error ε with failure probability at most δ in worst-case bit time polynomial in the input length, $`\varepsilon ^{-1}`$, and $`\log\delta^{-1}`$. We prove the perfect-matching entropy conjecture of Anari, Oveis Gharan, and Vinzant. For every feasible vector x of perfect-matching edge marginals in a loopless labelled multigraph on $`2m\ge2`$ vertices, the maximum entropy $`H(x)`$ of a matching law with marginals x satisfies
- notes: OpenAI math result family 113, Approximate counting and entropy of perfect matchings -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/113.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LoopMatching.fullEndpoint
- source_theorem_count: 1
- source_solution_module: OAI.Computability.LoopMatching.Endpoint
- source_main_result: OAI.LoopMatching.fullEndpoint
- source_papers: preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf preprints/Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026/main.pdf
- source_scope_note: lean/docs/113.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

universe u_1 u_2

namespace MatchingEntropy
structure LooplessGraph (V : Type u_1) (E : Type u_2) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e
namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
def Incident (G : LooplessGraph V E) (v : V) (e : E) : Prop :=
  G.left e=v ∨ G.right e=v
end LooplessGraph
end MatchingEntropy

namespace BinaryMatching
abbrev Pair (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
def completeGraph (n : ℕ) : MatchingEntropy.LooplessGraph (Fin n) (Pair n) where
  left e := e.val.1
  right e := e.val.2
  loopless e := ne_of_lt e.property

structure Record where
  left : ℕ
  right : ℕ
  multiplicity : ℕ
  deriving DecidableEq

structure Input where
  n : ℕ
  records : List Record
  valid : ∀ e∈records, e.left < e.right ∧ e.right < n
  unique : (records.map (fun e => (e.left,e.right))).Nodup

def multiplicity (G : Input) (e : Pair G.n) : ℕ :=
  match G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
  | none => 0
  | some r => r.multiplicity


def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length false ++ true :: n.bits

def encodeRecord (r : Record) : List Bool :=
  encodeNat r.left ++ encodeNat r.right ++ encodeNat r.multiplicity

def encodeInput (G : Input) : List Bool :=
  encodeNat G.n ++ encodeNat G.records.length ++ G.records.flatMap encodeRecord

end BinaryMatching

open scoped BigOperators

namespace LoopMatching

structure LoopRecord where
  vertex : ℕ
  multiplicity : ℕ
  deriving DecidableEq

structure Input where
  ordinary : BinaryMatching.Input
  loops : List LoopRecord
  valid : ∀ e ∈ loops, e.vertex < ordinary.n
  unique : (loops.map LoopRecord.vertex).Nodup

abbrev Input.n (G : Input) : ℕ := G.ordinary.n

def loopMultiplicity (G : Input) (v : Fin G.n) : ℕ :=
  match G.loops.find? (fun r => r.vertex == v.val) with
  | none => 0
  | some r => r.multiplicity

def IsPartialMatching (n : ℕ) (M : Finset (BinaryMatching.Pair n)) : Prop :=
  ∀ v : Fin n, ∀ e ∈ M, ∀ f ∈ M,
    (BinaryMatching.completeGraph n).Incident v e →
    (BinaryMatching.completeGraph n).Incident v f → e = f

abbrev PartialMatching (n : ℕ) :=
  { M : Finset (BinaryMatching.Pair n) // IsPartialMatching n M }

noncomputable instance partialMatchingFintype (n : ℕ) : Fintype (PartialMatching n) :=
  Fintype.ofFinite _

noncomputable def loopVertices {n : ℕ} (M : PartialMatching n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v =>
    ∀ e ∈ M.val, ¬ (BinaryMatching.completeGraph n).Incident v e)

noncomputable def weight (G : Input) (M : PartialMatching G.n) : ℕ :=
  (∏ e ∈ M.val, BinaryMatching.multiplicity G.ordinary e) *
    ∏ v ∈ loopVertices M, loopMultiplicity G v

noncomputable def count (G : Input) : ℕ := ∑ M : PartialMatching G.n, weight G M


def encodeLoopRecord (r : LoopRecord) : List Bool :=
  BinaryMatching.encodeNat r.vertex ++ BinaryMatching.encodeNat r.multiplicity

def encodeInput (G : Input) : List Bool :=
  BinaryMatching.encodeInput G.ordinary ++
    BinaryMatching.encodeNat G.loops.length ++ G.loops.flatMap encodeLoopRecord

def encodeOutput (a : ℕ × ℕ) : List Bool :=
  BinaryMatching.encodeNat a.1 ++ BinaryMatching.encodeNat a.2


def FullEndpoint : Prop :=
  ∃ A : Input → ℕ × ℕ,
    ∃ machine : Turing.TM2ComputableInPolyTime encodeInput encodeOutput A,
      (∀ k, Finite (machine.tm.Γ k)) ∧
      (∃ P : Polynomial ℕ, ∀ G,
        (encodeOutput (A G)).length ≤ P.eval (encodeInput G).length) ∧
      ∀ G, 0 < (A G).2 ∧
        (A G).1 ≤ (A G).2 * count G ∧
        (A G).2 * count G ≤ 2 ^ (18 * G.n) * (A G).1 ∧
        ((A G).1 = 0 ↔ count G = 0)

end LoopMatching

namespace LoopMatching

/-- A finite-alphabet polynomial-time rational approximation for singleton-loop matchings. -/
def fullEndpoint_statement : Prop :=
  FullEndpoint

end LoopMatching

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LoopMatching.fullEndpoint_statement

end Problem

/- Formalization scope, from lean/docs/113.md: The formalization gives a fully polynomial randomized approximation scheme for counting perfect matchings in every finite simple undirected graph. For rational $0<\varepsilon<1$ and $0<\delta<1/2$, it returns a nonnegative rational estimate with relative error at most $\varepsilon$ with probability at least $1-\delta$. If the graph has no perfect matching, every execution returns zero. The algorithm is a fixed finite-alphabet randomized machine. Its worst-case running time is polynomial in the binary input length, $\varepsilon^{-1}$, and $\log(\delta^{-1})$, including on unsuccessful random tapes. For feasible edge marginals $x$ of perfect matchings in a loopless multigraph on $2m$ vertices, let $F(x)=-\sum_e x_e\log x_e$, $B(x)=-\sum_e(1-x_e)\log(1-x_e)$, and let $H(x)$ be the maximum entropy of a matching law with those marginals. The formalization proves $F(x)-(2-2/m)B(x)\le H(x)\le F(x)$ for $m\ge1$, including boundary points of the polytope. It retains the earlier coefficient-eight entropy bound and the deterministic counting approximations with factors $512^n$ for loopless graphs and $2^{18n}$ with singleton loops. A further statement identifies the exact face obtained by expanding a degree-three vertex into a triangle and shows that minimal faces are carried to minimal faces by the expansion. The paper's sharp global face-dimension bound is not part of that selected statement. -/
