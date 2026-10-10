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

- problem_id: UniqueGamesTheorem
- collection: openai-math
- question_id: openai-math:102
- source: openai-math
- source_locator: lean/ComparatorChallenges/UniqueGamesTheorem.lean#OAI.UniqueGamesTheorem.theorem11
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Khot's Unique Games Conjecture. Independent direct reductions also establish NP-hardness, on unweighted graphs, of approximation beyond the Goemans–Williamson ratio for Max-Cut, below factor two for Vertex Cover, and within any fixed constant factor for Min-UnCut and directed feedback vertex set. These direct proofs use established PCP and Label Cover hardness results. ([Lean](lean/docs/102.md)) We prove the Unique Games Conjecture. For every fixed $`\varepsilon,\delta\in(0,1/2)`$, we give a deterministic polynomial-time reduction from 3SAT to Unique Games over a fixed finite alphabet, with completeness at least $`1-\varepsilon`$ and soundness at most δ. We prove that approximating Max-Cut on simple unweighted graphs within any fixed factor greater than the Goemans–Williamson constant is NP-hard. We prove that minimum Vertex Cover is NP-hard to approximate within every fixed factor below two, even on simple unweighted graphs. For every fixed C &gt; 1, approximating Min-UnCut within factor C is NP-hard, even on simple undirected unweighted graphs. Approximating minimum directed feedback vertex set within any fixed constant factor is NP-hard, even on unweighted digraphs.
- notes: OpenAI math result family 102, The Unique Games Conjecture and optimal approximation thresholds -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/102.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.UniqueGamesTheorem.theorem11
- source_theorem_count: 1
- source_solution_module: OAI.Computability.UniqueGames.Main
- source_main_result: OAI.UniqueGamesTheorem.theorem11
- source_papers: preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf
- source_scope_note: lean/docs/102.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace UniqueGamesTheorem.Foundations.Target

/-- Finite forward and inverse tables make totality and invertibility explicit.
An eventual external encoding only needs to serialize the forward table. -/
structure PermutationTable (alphabet : Nat) where
  images : Vector (Fin alphabet) alphabet
  inverseImages : Vector (Fin alphabet) alphabet
  leftInverse : ∀ label : Fin alphabet, inverseImages[images[label]] = label
  rightInverse : ∀ label : Fin alphabet, images[inverseImages[label]] = label

structure Constraint (vertices alphabet : Nat) where
  source : Fin vertices
  target : Fin vertices
  permutation : PermutationTable alphabet

def Constraint.satisfied {n q : Nat} (constraint : Constraint n q)
    (labeling : Fin n → Fin q) : Bool :=
  decide (constraint.permutation.images[labeling constraint.source] = labeling constraint.target)

/-- Constraint occurrences are list entries, so repeated parallel edges retain
their multiplicity. No weights are hidden in this representation. -/
structure Instance (alphabet : Nat) where
  vertices : Nat
  constraints : List (Constraint vertices alphabet)
  nonempty : constraints ≠ []

def countSatisfied {n q : Nat} (labeling : Fin n → Fin q) :
    List (Constraint n q) → Nat
  | [] => 0
  | constraint :: rest =>
      (if constraint.satisfied labeling then 1 else 0) + countSatisfied labeling rest

end UniqueGamesTheorem.Foundations.Target

namespace UniqueGamesTheorem.BinaryFormula

open UniqueGamesTheorem.Foundations

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

/-- An ordinary conjunction of three-slot clauses with sparse variable names.
Repeated names and repeated literals are permitted in every clause. -/
structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

end UniqueGamesTheorem.BinaryFormula

namespace UniqueGamesTheorem.BinaryEncoding

open BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bits, trailing) ← parseFrame rest
      return (b :: bits, trailing)
  | _ => none

/-- Equality with the canonical digits rejects alternate padded encodings. -/
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

/-- Fuel bounds the number of clause iterations, not the size of any name. -/
def parseClauses : Nat → List Bool → Option (List Clause × List Bool)
  | 0, _ => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

end UniqueGamesTheorem.BinaryEncoding

namespace UniqueGamesTheorem.BinaryLanguage

open UniqueGamesTheorem.Foundations

def language (input : List Bool) : Prop :=
  ∃ formula, BinaryEncoding.decodeFormula input = some formula ∧ formula.Satisfiable

end UniqueGamesTheorem.BinaryLanguage

namespace UniqueGamesTheorem.Integration.BinaryLinear

abbrev F2 := ZMod 2

abbrev Vector (n : Nat) := Fin n → F2

end UniqueGamesTheorem.Integration.BinaryLinear

namespace UniqueGamesTheorem.Integration.TranslationTarget

open UniqueGamesTheorem.Foundations
open Target

def IsTranslationInstance {q s : Nat} (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (g : Instance q) : Prop :=
  ∀ constraint ∈ g.constraints, ∃ shift : BinaryLinear.Vector s,
    ∀ label : Fin q,
      coordinates (constraint.permutation.images[label]) = coordinates label + shift

end UniqueGamesTheorem.Integration.TranslationTarget

namespace UniqueGamesTheorem.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

end UniqueGamesTheorem.Foundations.Complexity

namespace UniqueGamesTheorem.Foundations.Complexity

open Target

def tableWords {q : Nat} (table : PermutationTable q) : List Nat :=
  table.images.toList.map Fin.val

def constraintWords {n q : Nat} (constraint : Constraint n q) : List Nat :=
  [constraint.source.val, constraint.target.val] ++ tableWords constraint.permutation

def gameWords {q : Nat} (game : Instance q) : List Nat :=
  [game.vertices, q, game.constraints.length] ++ game.constraints.flatMap constraintWords

def gameBits {q : Nat} (game : Instance q) : List Bool := encodeWords (gameWords game)

end UniqueGamesTheorem.Foundations.Complexity

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

open Turing

/-- Every physical tape has a finite alphabet. Together with `M.kFin`, this
also makes the disjoint union of all physical tape alphabets finite. -/
def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

namespace UniqueGamesTheorem.Explicit.MachineOutputContract

open UniqueGamesTheorem.Foundations
open Target
open scoped BigOperators

/-- A canonical orientation from the false side to the true side. Injectivity
is on occurrence indices, so two distinct list entries cannot be parallel even
when their constraint tables are different. -/
structure SimpleBipartite {q : Nat} (game : Instance q) where
  side : Fin game.vertices → Bool
  sourceSide : ∀ i : Fin game.constraints.length,
    side game.constraints[i].source = false
  targetSide : ∀ i : Fin game.constraints.length,
    side game.constraints[i].target = true
  endpoints_injective : Function.Injective (fun i : Fin game.constraints.length =>
    (game.constraints[i].source, game.constraints[i].target))

/-- Every parameter, coordinate identification, program, and polynomial is
fixed before the input quantifier. The identity input encoding measures runtime
in the original raw bit length, including sparse binary variable names. -/
structure BinaryGapReduction (ε δ : ℝ) where
  alphabet : Nat
  alphabetAtLeastTwo : 2 ≤ alphabet
  dimension : Nat
  dimensionPositive : 1 ≤ dimension
  coordinates : Fin alphabet ≃ Integration.BinaryLinear.Vector dimension
  construct : List Bool → Instance alphabet
  simpleBipartite : ∀ input, SimpleBipartite (construct input)
  translations : ∀ input,
    Integration.TranslationTarget.IsTranslationInstance coordinates (construct input)
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    Complexity.gameBits construct
  finiteAlphabet : Complexity.MachineFiniteAlphabet.FiniteAlphabet computation.tm
  completeness : ∀ input, BinaryLanguage.language input →
    ∃ labeling, 1 - ε ≤
      (countSatisfied labeling (construct input).constraints : ℝ) /
        (construct input).constraints.length
  soundness : ∀ input, ¬BinaryLanguage.language input →
    ∀ labeling, (countSatisfied labeling (construct input).constraints : ℝ) /
      (construct input).constraints.length ≤ δ

end UniqueGamesTheorem.Explicit.MachineOutputContract

namespace UniqueGamesTheorem

/-- For every fixed pair of errors in `(0, 1/2)`, binary 3SAT reduces in
polynomial time to translation Unique Games with completeness at least `1 - ε`
and soundness at most `δ`. The alphabet and machine depend only on the errors. -/
def theorem11_statement : Prop :=
  ∀ (ε δ : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hδ : 0 < δ) (hδhalf : δ < 1 / 2),
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ)

end UniqueGamesTheorem

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.UniqueGamesTheorem.theorem11_statement

end Problem

/- Formalization scope, from lean/docs/102.md: The Unique Games conjecture asks for hardness of distinguishing nearly satisfiable unique games from games of very small value. The formalized result gives, for every fixed $0<\varepsilon,\delta<1/2$, a deterministic polynomial-time reduction from binary 3SAT to nonempty unweighted simple bipartite unique games. Satisfiable inputs have value at least $1-\varepsilon$ and unsatisfiable inputs have value at most $\delta$. The alphabet is a fixed $\mathbb F_2^s$ depending only on the errors, and every constraint is a translation. The formalized result establishes hardness of approximating Max-Cut beyond the Goemans–Williamson constant $\alpha_{\mathrm{GW}}$. For every fixed $\alpha_{\mathrm{GW}}<\alpha\le1$, it gives a deterministic polynomial-time reduction from binary 3SAT to a strictly separated Max-Cut gap on finite simple unweighted graphs. The reduction includes the explicit positive integer scaling used in the gap statement. The formalized result gives the factor-two hardness threshold for Vertex Cover. For each integer $m\ge4$, a polynomial-time reduction from binary 3SAT produces simple unweighted graphs with cover density below $1/2+1/m$ on satisfiable inputs and above $1-1/m$ on unsatisfiable inputs. Consequently, any polynomial-time approximation with a fixed factor $1\le\alpha<2$ would give a polynomial-time decision algorithm for 3SAT. No assumption that $P\ne NP$ is built into the statement. Min-UnCut minimizes the number of edges left uncut by a bipartition. The formalization constructs a deterministic reduction from encoded $3$-SAT formulas to finite simple unweighted Min-UnCut instances with arbitrarily large fixed multiplicative gaps. For every integer $K\ge2$, satisfiable formulas give optimum at most the output threshold, while unsatisfiable formulas give optimum strictly greater than $K$ times that threshold. Runtime and output length are polynomial for each fixed $K$, establishing hardness for every fixed approximation factor greater than one. A directed feedback vertex set meets every directed cycle. The formalization proves hardness of approximating the minimum such set within any fixed constant factor. For every real factor $A\ge1$ and every language in NP, it constructs a polynomial-time gap reduction to unweighted directed graphs with the stated completeness and soundness separation. Thus a fixed-factor polynomial-time approximation would imply a polynomial-time algorithm for every NP language. -/
