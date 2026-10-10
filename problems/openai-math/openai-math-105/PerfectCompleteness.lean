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

- problem_id: PerfectCompleteness
- collection: openai-math
- question_id: openai-math:105
- source: openai-math
- source_locator: lean/ComparatorChallenges/PerfectCompleteness.lean#OAI.PerfectCompleteness.Theorem11.exists_reduction
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Khot's 2-to-1 Games Conjecture with perfect completeness: for every fixed rational $`\delta\in(0,1)`$, it is NP-hard to distinguish satisfiable games from games whose optimum is at most δ, on explicit unweighted instances. The alphabet depends only on δ, and every right-hand label has exactly two preimages under each constraint map. ([Lean](lean/docs/105.md)) We prove the 2-to-1 Games Conjecture with perfect completeness. For every fixed rational $`\delta\in(0,1)`$, it is NP-hard to distinguish satisfiable 2-to-1 games from games of value at most δ, with a fixed alphabet and an explicitly listed unweighted multiset of constraints.
- notes: OpenAI math result family 105, Perfect completeness for 2-to-1 games -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/105.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PerfectCompleteness.Theorem11.exists_reduction
- source_theorem_count: 1
- source_solution_module: OAI.Computability.PerfectCompleteness.Main
- source_main_result: OAI.PerfectCompleteness.Theorem11.exists_reduction
- source_papers: preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf
- source_scope_note: lean/docs/105.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

end UniqueGamesTheorem.Foundations.Complexity

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

open Turing

def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

namespace PerfectCompleteness.BinaryFormula

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

end PerfectCompleteness.BinaryFormula

namespace PerfectCompleteness.BinaryEncoding

open PerfectCompleteness.BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bits, trailing) ← parseFrame rest
      return (b :: bits, trailing)
  | _ => none

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
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

end PerfectCompleteness.BinaryEncoding

namespace PerfectCompleteness.BinaryLanguage

def language (input : List Bool) : Prop :=
  ∃ formula, BinaryEncoding.decodeFormula input = some formula ∧ formula.Satisfiable

end PerfectCompleteness.BinaryLanguage

namespace PerfectCompleteness

structure ProjectionTable (q : Nat) where
  images : Vector (Fin q) (2 * q)
  exactlyTwo : ∀ b : Fin q,
    ((List.finRange (2 * q)).filter (fun a => decide (images[a] = b))).length = 2

structure Edge (leftVertices rightVertices q : Nat) where
  left : Fin leftVertices
  right : Fin rightVertices
  projection : ProjectionTable q

structure Instance (q : Nat) where
  leftVertices : Nat
  rightVertices : Nat
  edges : List (Edge leftVertices rightVertices q)
  nonempty : edges ≠ []

abbrev Labeling {q : Nat} (G : Instance q) :=
  (Fin G.leftVertices → Fin (2 * q)) × (Fin G.rightVertices → Fin q)

def Edge.satisfied {l r q : Nat} (e : Edge l r q)
    (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) : Bool :=
  decide (e.projection.images[a e.left] = b e.right)

def countSatisfied {l r q : Nat} (a : Fin l → Fin (2 * q))
    (b : Fin r → Fin q) : List (Edge l r q) → Nat
  | [] => 0
  | e :: es => (if e.satisfied a b then 1 else 0) + countSatisfied a b es

end PerfectCompleteness

namespace PerfectCompleteness.Instance

def maxSatisfied {q : Nat} (G : Instance q) : Nat :=
  Finset.univ.sup (fun s : Labeling G => countSatisfied s.1 s.2 G.edges)

noncomputable def value {q : Nat} (G : Instance q) : ℝ :=
  (G.maxSatisfied : ℝ) / G.edges.length

end PerfectCompleteness.Instance

namespace PerfectCompleteness.Encoding

open UniqueGamesTheorem.Foundations.Complexity

def tableWords {q : Nat} (table : ProjectionTable q) : List Nat :=
  table.images.toList.map Fin.val

def edgeWords {l r q : Nat} (edge : Edge l r q) : List Nat :=
  [edge.left.val, edge.right.val] ++ tableWords edge.projection

def gameWords {q : Nat} (game : Instance q) : List Nat :=
  [game.leftVertices, game.rightVertices, q, game.edges.length] ++
    game.edges.flatMap edgeWords

def gameBits {q : Nat} (game : Instance q) : List Bool :=
  encodeWords (gameWords game)

end PerfectCompleteness.Encoding

namespace PerfectCompleteness

open Turing UniqueGamesTheorem.Foundations.Complexity

structure BinaryGapReduction (δ : ℚ) where
  alphabet : Nat
  alphabet_ge_two : 2 ≤ alphabet
  construct : List Bool → Instance alphabet
  computation : TM2ComputableInPolyTime (id : List Bool → List Bool)
    Encoding.gameBits construct
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  completeness : ∀ input, BinaryLanguage.language input → (construct input).value = 1
  soundness : ∀ input, ¬BinaryLanguage.language input → (construct input).value ≤ (δ : ℝ)

end PerfectCompleteness

namespace PerfectCompleteness.Theorem11

def exists_reduction_statement : Prop :=
  ∀ (δ : ℚ) (positive : 0 < δ) (less_than_one : δ < 1),
    Nonempty (PerfectCompleteness.BinaryGapReduction δ)

end PerfectCompleteness.Theorem11

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PerfectCompleteness.Theorem11.exists_reduction_statement

end Problem

/- Formalization scope, from lean/docs/105.md: The formalized result establishes perfect-completeness hardness for 2-to-1 games. For every fixed rational $0<\delta<1$, a deterministic polynomial-time reduction from binary 3SAT produces a nonempty unweighted game of value exactly $1$ on satisfiable inputs and at most $\delta$ on unsatisfiable inputs. Each constraint projection has exactly two preimages for each output label. The alphabet depends only on $\delta$, and the runtime is measured in the original input bit length. -/
