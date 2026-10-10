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

- problem_id: DirectedFeedback
- collection: openai-math
- question_id: openai-math:102
- source: openai-math
- source_locator: lean/ComparatorChallenges/DirectedFeedback.lean#OAI.DirectedFeedback.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Khot's Unique Games Conjecture. Independent direct reductions also establish NP-hardness, on unweighted graphs, of approximation beyond the Goemans–Williamson ratio for Max-Cut, below factor two for Vertex Cover, and within any fixed constant factor for Min-UnCut and directed feedback vertex set. These direct proofs use established PCP and Label Cover hardness results. ([Lean](lean/docs/102.md)) We prove the Unique Games Conjecture. For every fixed $`\varepsilon,\delta\in(0,1/2)`$, we give a deterministic polynomial-time reduction from 3SAT to Unique Games over a fixed finite alphabet, with completeness at least $`1-\varepsilon`$ and soundness at most δ. We prove that approximating Max-Cut on simple unweighted graphs within any fixed factor greater than the Goemans–Williamson constant is NP-hard. We prove that minimum Vertex Cover is NP-hard to approximate within every fixed factor below two, even on simple unweighted graphs. For every fixed C &gt; 1, approximating Min-UnCut within factor C is NP-hard, even on simple undirected unweighted graphs. Approximating minimum directed feedback vertex set within any fixed constant factor is NP-hard, even on unweighted digraphs.
- notes: OpenAI math result family 102, The Unique Games Conjecture and optimal approximation thresholds -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/102.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.DirectedFeedback.main
- source_theorem_count: 1
- source_solution_module: OAI.Computability.DirectedFeedback.Main
- source_papers: preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf
- source_scope_note: lean/docs/102.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace DirectedFeedback

/-- Unary self-delimiting natural numbers. Outputs are explicit, not succinct. -/
def natBits (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- The explicit framing used for an input and its NP certificate. -/
def pairBits (p : List Bool × List Bool) : List Bool :=
  natBits p.1.length ++ p.1 ++ p.2

/-- Finitely many stacks and control states are already part of `FinTM2`.
This additionally excludes infinite stack alphabets. -/
def FiniteAlphabet (M : Turing.FinTM2) : Prop := ∀ k, Finite (M.Γ k)

/-- Polynomially bounded certificates checked by an actual deterministic
finite-alphabet machine, on the explicitly encoded input/certificate pair. -/
structure NPVerifier where
  witnessBound : Polynomial ℕ
  verify : (List Bool × List Bool) → Bool
  computation : Turing.TM2ComputableInPolyTime pairBits (fun b : Bool => [b]) verify
  finiteAlphabet : FiniteAlphabet computation.tm

def NPVerifier.Accepts (V : NPVerifier) (input : List Bool) : Prop :=
  ∃ witness : List Bool, witness.length ≤ V.witnessBound.eval input.length ∧
    V.verify (input, witness) = true

/-- NP is defined independently of SAT or any hardness assertion. -/
def InNP (language : List Bool → Prop) : Prop :=
  ∃ V : NPVerifier, ∀ input, language input ↔ V.Accepts input

/-- Finite loopless digraph. Opposite arcs are permitted. Every arc is listed
explicitly. No symmetric closure or undirected-cycle convention is used. -/
structure Digraph where
  n : ℕ
  arcs : List (Fin n × Fin n)
  loopless : ∀ e ∈ arcs, e.1 ≠ e.2
  nodup : arcs.Nodup

namespace Digraph

/-- An actual simple directed cycle of positive length. A cyclic enumeration
of `r + 1` distinct vertices supplies every successive arc, including the
closing arc. A 2-cycle is allowed; looplessness rules out length 1. -/
def IsCycle (G : Digraph) {r : ℕ} (c : Fin (r + 1) → Fin G.n) : Prop :=
  Function.Injective c ∧ ∀ i, (c i, c (i + 1)) ∈ G.arcs

/-- A feedback set intersects EVERY actual directed cycle. -/
def Feedback (G : Digraph) (F : Finset (Fin G.n)) : Prop :=
  ∀ (r : ℕ) (c : Fin (r + 1) → Fin G.n), G.IsCycle c → ∃ i, c i ∈ F

/-- Minimum number of vertices of a feedback set. No weights or auxiliary
cost oracle appear in this definition. -/
noncomputable def dfvs (G : Digraph) : ℕ := by
  classical
  exact Nat.find (show ∃ k : ℕ, ∃ F : Finset (Fin G.n), G.Feedback F ∧ F.card = k from
    ⟨G.n, Finset.univ, by
      intro r c _
      exact ⟨0, Finset.mem_univ _⟩, by simp⟩)

/-- Full explicit vertex and arc serialization, including isolated vertices. -/
def bits (G : Digraph) : List Bool :=
  ([G.n] ++ List.range G.n ++ [G.arcs.length] ++
    G.arcs.flatMap (fun e => [e.1.val, e.2.val])).flatMap natBits

end Digraph

/-- Output includes a strictly positive integer threshold. -/
structure GapInstance where
  graph : Digraph
  k : ℕ
  k_pos : 0 < k

def GapInstance.bits (I : GapInstance) : List Bool :=
  natBits I.k ++ I.graph.bits

/-- A strict YES/NO gap reduction implemented by a finite-alphabet machine
with polynomial runtime in the raw input bit length. -/
structure GapReduction (A : ℝ) (language : List Bool → Prop) where
  construct : List Bool → GapInstance
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    GapInstance.bits construct
  finiteAlphabet : FiniteAlphabet computation.tm
  completeness : ∀ input, language input →
    (construct input).graph.dfvs ≤ (construct input).k
  soundness : ∀ input, ¬ language input →
    A * ((construct input).k : ℝ) < ((construct input).graph.dfvs : ℝ)

/-- Constant-factor directed feedback vertex set hardness for all NP languages. -/
def MainStatement : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∀ language : List Bool → Prop,
    InNP language → Nonempty (GapReduction A language)

end DirectedFeedback

def DirectedFeedback.main_statement : Prop :=
  DirectedFeedback.MainStatement

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DirectedFeedback.main_statement

end Problem

/- Formalization scope, from lean/docs/102.md: The Unique Games conjecture asks for hardness of distinguishing nearly satisfiable unique games from games of very small value. The formalized result gives, for every fixed $0<\varepsilon,\delta<1/2$, a deterministic polynomial-time reduction from binary 3SAT to nonempty unweighted simple bipartite unique games. Satisfiable inputs have value at least $1-\varepsilon$ and unsatisfiable inputs have value at most $\delta$. The alphabet is a fixed $\mathbb F_2^s$ depending only on the errors, and every constraint is a translation. The formalized result establishes hardness of approximating Max-Cut beyond the Goemans–Williamson constant $\alpha_{\mathrm{GW}}$. For every fixed $\alpha_{\mathrm{GW}}<\alpha\le1$, it gives a deterministic polynomial-time reduction from binary 3SAT to a strictly separated Max-Cut gap on finite simple unweighted graphs. The reduction includes the explicit positive integer scaling used in the gap statement. The formalized result gives the factor-two hardness threshold for Vertex Cover. For each integer $m\ge4$, a polynomial-time reduction from binary 3SAT produces simple unweighted graphs with cover density below $1/2+1/m$ on satisfiable inputs and above $1-1/m$ on unsatisfiable inputs. Consequently, any polynomial-time approximation with a fixed factor $1\le\alpha<2$ would give a polynomial-time decision algorithm for 3SAT. No assumption that $P\ne NP$ is built into the statement. Min-UnCut minimizes the number of edges left uncut by a bipartition. The formalization constructs a deterministic reduction from encoded $3$-SAT formulas to finite simple unweighted Min-UnCut instances with arbitrarily large fixed multiplicative gaps. For every integer $K\ge2$, satisfiable formulas give optimum at most the output threshold, while unsatisfiable formulas give optimum strictly greater than $K$ times that threshold. Runtime and output length are polynomial for each fixed $K$, establishing hardness for every fixed approximation factor greater than one. A directed feedback vertex set meets every directed cycle. The formalization proves hardness of approximating the minimum such set within any fixed constant factor. For every real factor $A\ge1$ and every language in NP, it constructs a polynomial-time gap reduction to unweighted directed graphs with the stated completeness and soundness separation. Thus a fixed-factor polynomial-time approximation would imply a polynomial-time algorithm for every NP language. -/
