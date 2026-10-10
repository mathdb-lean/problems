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

- problem_id: VertexCover
- collection: openai-math
- question_id: openai-math:102
- source: openai-math
- source_locator: lean/ComparatorChallenges/VertexCover.lean#OAI.VertexCover.explicit_cover_gap
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Khot's Unique Games Conjecture. Independent direct reductions also establish NP-hardness, on unweighted graphs, of approximation beyond the Goemans–Williamson ratio for Max-Cut, below factor two for Vertex Cover, and within any fixed constant factor for Min-UnCut and directed feedback vertex set. These direct proofs use established PCP and Label Cover hardness results. ([Lean](lean/docs/102.md)) We prove the Unique Games Conjecture. For every fixed $`\varepsilon,\delta\in(0,1/2)`$, we give a deterministic polynomial-time reduction from 3SAT to Unique Games over a fixed finite alphabet, with completeness at least $`1-\varepsilon`$ and soundness at most δ. We prove that approximating Max-Cut on simple unweighted graphs within any fixed factor greater than the Goemans–Williamson constant is NP-hard. We prove that minimum Vertex Cover is NP-hard to approximate within every fixed factor below two, even on simple unweighted graphs. For every fixed C &gt; 1, approximating Min-UnCut within factor C is NP-hard, even on simple undirected unweighted graphs. Approximating minimum directed feedback vertex set within any fixed constant factor is NP-hard, even on unweighted digraphs.
- notes: OpenAI math result family 102, The Unique Games Conjecture and optimal approximation thresholds -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/102.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.VertexCover.explicit_cover_gap OAI.VertexCover.every_fixed_factor_below_two
- source_theorem_count: 2
- source_solution_module: OAI.Computability.VertexCover.Main
- source_main_result: OAI.VertexCover.every_fixed_factor_below_two
- source_papers: preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf
- source_scope_note: lean/docs/102.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace UniqueGames.BinaryFormula

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

end UniqueGames.BinaryFormula

namespace UniqueGames.BinaryEncoding

open BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bits, trailing) ← parseFrame rest
      return (b :: bits, trailing)
  | _ => none

def nameBits (name : Nat) : List Bool := frame name.bits

def parseName (input : List Bool) : Option (Nat × List Bool) := do
  let (digits, rest) ← parseFrame input
  let name := bitsValue digits
  if digits = name.bits then some (name, rest) else none

def parseLiteral : List Bool → Option (Literal × List Bool)
  | sign :: input => do
      let (name, rest) ← parseName input
      return (⟨name, sign⟩, rest)
  | [] => none

def parseClause (input : List Bool) : Option (Clause × List Bool) := do
  let (a, input) ← parseLiteral input
  let (b, input) ← parseLiteral input
  let (c, rest) ← parseLiteral input
  return (#v[a, b, c], rest)

def parseClauses : Nat → List Bool → Option (List Clause × List Bool)
  | 0, _ => none
  | _fuel + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

end UniqueGames.BinaryEncoding

namespace VertexCover

def ThreeSAT (input : List Bool) : Prop :=
  ∃ formula, UniqueGames.BinaryEncoding.decodeFormula input = some formula ∧
    formula.Satisfiable

structure ExplicitGraph where
  n : ℕ
  edges : List (Fin n × Fin n)
  increasing : ∀ e ∈ edges, e.1 < e.2
  nodup : edges.Nodup

namespace ExplicitGraph

def Cover (G : ExplicitGraph) (S : Finset (Fin G.n)) : Prop :=
  ∀ e ∈ G.edges, e.1 ∈ S ∨ e.2 ∈ S

instance (G : ExplicitGraph) (S : Finset (Fin G.n)) : Decidable (G.Cover S) :=
  inferInstanceAs (Decidable (∀ e ∈ G.edges, e.1 ∈ S ∨ e.2 ∈ S))

noncomputable def coverNumber (G : ExplicitGraph) : ℕ :=
  Nat.find (show ∃ k : ℕ, ∃ S : Finset (Fin G.n), G.Cover S ∧ S.card = k from
    ⟨G.n, Finset.univ, by simp [Cover], by simp⟩)

def bits (G : ExplicitGraph) : List Bool :=
  let names := [G.n] ++ List.range G.n ++ [G.edges.length] ++
    G.edges.flatMap (fun e => [e.1.val, e.2.val])
  names.flatMap UniqueGames.BinaryEncoding.nameBits

end ExplicitGraph

def FiniteAlphabet (M : Turing.FinTM2) : Prop := ∀ k, Finite (M.Γ k)

structure GapReduction (m : ℕ) where
  construct : List Bool → ExplicitGraph
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    ExplicitGraph.bits construct
  finiteAlphabet : FiniteAlphabet computation.tm
  completeness : ∀ input, ThreeSAT input →
    ((construct input).coverNumber : ℝ) <
      (1 / 2 + 1 / (m : ℝ)) * (construct input).n
  soundness : ∀ input, ¬ ThreeSAT input →
    (1 - 1 / (m : ℝ)) * (construct input).n <
      ((construct input).coverNumber : ℝ)

def natListBits (L : List ℕ) : List Bool :=
  (L.length :: L).flatMap UniqueGames.BinaryEncoding.nameBits

structure Approximation (α : ℝ) where
  run : ExplicitGraph → List ℕ
  computation : Turing.TM2ComputableInPolyTime ExplicitGraph.bits natListBits run
  finiteAlphabet : FiniteAlphabet computation.tm
  nodup : ∀ G, (run G).Nodup
  vertices : ∀ G, ∀ v ∈ run G, v < G.n
  covers : ∀ G, ∀ e ∈ G.edges, e.1.val ∈ run G ∨ e.2.val ∈ run G
  quality : ∀ G, ((run G).length : ℝ) ≤ α * (G.coverNumber : ℝ)

structure ThreeSATDecision where
  run : List Bool → Bool
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    (fun b : Bool => [b]) run
  finiteAlphabet : FiniteAlphabet computation.tm
  correct : ∀ input, run input = true ↔ ThreeSAT input

def explicit_cover_gap_statement : Prop :=
  ∀ (m : ℕ) (hm : 4 ≤ m),
    Nonempty (GapReduction m)

def every_fixed_factor_below_two_statement : Prop :=
  ∀ (α : ℝ) (hα : 1 ≤ α) (hα2 : α < 2) (algorithm : Approximation α),
    Nonempty ThreeSATDecision

end VertexCover

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.VertexCover.explicit_cover_gap_statement ∧
  _root_.OAI.VertexCover.every_fixed_factor_below_two_statement

end Problem

/- Formalization scope, from lean/docs/102.md: The Unique Games conjecture asks for hardness of distinguishing nearly satisfiable unique games from games of very small value. The formalized result gives, for every fixed $0<\varepsilon,\delta<1/2$, a deterministic polynomial-time reduction from binary 3SAT to nonempty unweighted simple bipartite unique games. Satisfiable inputs have value at least $1-\varepsilon$ and unsatisfiable inputs have value at most $\delta$. The alphabet is a fixed $\mathbb F_2^s$ depending only on the errors, and every constraint is a translation. The formalized result establishes hardness of approximating Max-Cut beyond the Goemans–Williamson constant $\alpha_{\mathrm{GW}}$. For every fixed $\alpha_{\mathrm{GW}}<\alpha\le1$, it gives a deterministic polynomial-time reduction from binary 3SAT to a strictly separated Max-Cut gap on finite simple unweighted graphs. The reduction includes the explicit positive integer scaling used in the gap statement. The formalized result gives the factor-two hardness threshold for Vertex Cover. For each integer $m\ge4$, a polynomial-time reduction from binary 3SAT produces simple unweighted graphs with cover density below $1/2+1/m$ on satisfiable inputs and above $1-1/m$ on unsatisfiable inputs. Consequently, any polynomial-time approximation with a fixed factor $1\le\alpha<2$ would give a polynomial-time decision algorithm for 3SAT. No assumption that $P\ne NP$ is built into the statement. Min-UnCut minimizes the number of edges left uncut by a bipartition. The formalization constructs a deterministic reduction from encoded $3$-SAT formulas to finite simple unweighted Min-UnCut instances with arbitrarily large fixed multiplicative gaps. For every integer $K\ge2$, satisfiable formulas give optimum at most the output threshold, while unsatisfiable formulas give optimum strictly greater than $K$ times that threshold. Runtime and output length are polynomial for each fixed $K$, establishing hardness for every fixed approximation factor greater than one. A directed feedback vertex set meets every directed cycle. The formalization proves hardness of approximating the minimum such set within any fixed constant factor. For every real factor $A\ge1$ and every language in NP, it constructs a polynomial-time gap reduction to unweighted directed graphs with the stated completeness and soundness separation. Thus a fixed-factor polynomial-time approximation would imply a polynomial-time algorithm for every NP language. -/
