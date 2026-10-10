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

- problem_id: AlgorithmicThinTrees
- collection: openai-math
- question_id: openai-math:174
- source: openai-math
- source_locator: lean/ComparatorChallenges/AlgorithmicThinTrees.lean#OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the strong thin-tree conjecture constructively. Every finite loopless k-edge-connected multigraph on at least two vertices has a spanning tree containing at most a universal $`C/k`$ fraction of the edges of every cut. Such a tree can be found deterministically in polynomial time, even with binary-encoded parallel-edge multiplicities. ([Lean](lean/docs/174.md)) We prove that every finite loopless k-edge-connected multigraph on at least two vertices, with k ≥ 1, has a spanning tree meeting each cut in at most $`C/k`$ times the size of the cut, where C is a universal constant. This resolves the strong thin tree conjecture. We give a deterministic polynomial-time construction of strong thin trees. Given a finite k-edge-connected loopless multigraph on at least one vertex, the algorithm constructs a spanning tree meeting every cut in at most a $`C/k`$ fraction of its edges, for a universal constant C. The running time is polynomial in the binary input length, including when parallel-edge multiplicities are encoded in binary.
- notes: OpenAI math result family 174, Deterministic construction of strong thin spanning trees -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/174.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.ThinTrees.AlgorithmicMain
- source_papers: preprints/The-strong-thin-tree-conjecture-September-23-2026/paper.pdf preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf
- source_scope_note: lean/docs/174.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Deterministic polynomial-time construction of strong thin trees. -/

namespace StrongThinTree

structure MultiGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  loopless : ∀ e, left e ≠ right e

namespace MultiGraph

def cut {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m))
    (S : Finset (Fin n)) : Finset (Fin m) :=
  T.filter fun e => (G.left e ∈ S ∧ G.right e ∉ S) ∨
    (G.right e ∈ S ∧ G.left e ∉ S)

def Connected {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → (G.cut T S).Nonempty

def SpanningTree {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) : Prop :=
  G.Connected T ∧ ∀ e ∈ T, ¬ G.Connected (T.erase e)

def EdgeConnected {n m : ℕ} (G : MultiGraph n m) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    k ≤ (G.cut Finset.univ S).card

end MultiGraph
end StrongThinTree

namespace CurrentKS

def frame : List Bool → List Bool
  | [] => [true]
  | b :: bs => false :: b :: frame bs

def encodeNat (n : ℕ) : List Bool := frame (Computability.encodeNat n)

inductive StackAction where
  | stay
  | pop
  | push (bit : Bool)
  deriving DecidableEq

def StackAction.apply : StackAction → List Bool → List Bool
  | .stay, xs => xs
  | .pop, xs => xs.tail
  | .push b, xs => b :: xs

structure Instruction (k q : ℕ) where
  next : Option (Fin q)
  actions : Fin k → StackAction

def Instruction.halt (k q : ℕ) : Instruction k q := ⟨none, fun _ => .stay⟩

structure Machine where
  stackCount : ℕ
  states : ℕ
  initial : Fin states
  inputStack : Fin stackCount
  outputStack : Fin stackCount
  table : List (Instruction stackCount states)

structure Config (k q : ℕ) where
  state : Option (Fin q)
  «stacks» : Fin k → List Bool

def topCode : List Bool → ℕ
  | [] => 0
  | false :: _ => 1
  | true :: _ => 2

def headsCode : (k : ℕ) → (Fin k → List Bool) → ℕ
  | 0, _ => 0
  | k + 1, s => topCode (s 0) + 3 * headsCode k (fun j => s j.succ)

def Machine.step (M : Machine) (c : Config M.stackCount M.states) :
    Config M.stackCount M.states :=
  match c.state with
  | none => c
  | some q =>
    let instruction := M.table.getD
      (3 ^ M.stackCount * q.val + headsCode M.stackCount c.stacks)
      (Instruction.halt M.stackCount M.states)
    ⟨instruction.next, fun j => (instruction.actions j).apply (c.stacks j)⟩

def Machine.init (M : Machine) (input : List Bool) : Config M.stackCount M.states :=
  ⟨some M.initial, fun j => if j = M.inputStack then input else []⟩

def Machine.run (M : Machine) (input : List Bool) (fuel : ℕ) :
    Config M.stackCount M.states := (M.step^[fuel]) (M.init input)

end CurrentKS

namespace AlgorithmicThinTrees
open StrongThinTree

structure ExplicitInput where
  n : ℕ
  m : ℕ
  k : ℕ
  graph : MultiGraph n m

structure BinaryInput where
  n : ℕ
  p : ℕ
  k : ℕ
  left : Fin p → Fin n
  right : Fin p → Fin n
  ordered : ∀ i, left i < right i
  distinct : Function.Injective (fun i => (left i, right i))
  multiplicity : Fin p → ℕ

abbrev BinaryInput.Edge (x : BinaryInput) := Σ i : Fin x.p, Fin (x.multiplicity i)

noncomputable def BinaryInput.edgeEquiv (x : BinaryInput) :
    x.Edge ≃ Fin (Fintype.card x.Edge) := Fintype.equivFin x.Edge

noncomputable def BinaryInput.graph (x : BinaryInput) :
    MultiGraph x.n (Fintype.card x.Edge) where
  left e := x.left (x.edgeEquiv.symm e).1
  right e := x.right (x.edgeEquiv.symm e).1
  loopless e := ne_of_lt (x.ordered (x.edgeEquiv.symm e).1)

inductive Input where
  | explicit (x : ExplicitInput)
  | binary (x : BinaryInput)

def ExplicitInput.encode (x : ExplicitInput) : List Bool :=
  CurrentKS.encodeNat x.n ++ CurrentKS.encodeNat x.m ++ CurrentKS.encodeNat x.k ++
    (List.ofFn fun i : Fin x.m =>
      CurrentKS.encodeNat (x.graph.left i).val ++
      CurrentKS.encodeNat (x.graph.right i).val).flatten

def BinaryInput.encode (x : BinaryInput) : List Bool :=
  CurrentKS.encodeNat x.n ++ CurrentKS.encodeNat x.p ++ CurrentKS.encodeNat x.k ++
    (List.ofFn fun i : Fin x.p =>
      CurrentKS.encodeNat (x.left i).val ++ CurrentKS.encodeNat (x.right i).val ++
      CurrentKS.encodeNat (x.multiplicity i)).flatten

def Input.encode : Input → List Bool
  | .explicit x => false :: x.encode
  | .binary x => true :: x.encode

def Input.length (x : Input) : ℕ := x.encode.length

def Input.n : Input → ℕ
  | .explicit x => x.n
  | .binary x => x.n

def Valid : Input → Prop
  | .explicit x => 1 ≤ x.n ∧ 1 ≤ x.k ∧ x.graph.EdgeConnected x.k
  | .binary x => 1 ≤ x.n ∧ 1 ≤ x.k ∧ x.graph.EdgeConnected x.k

def ThinTree {n m : ℕ} (C : ℝ) (k : ℕ) (G : MultiGraph n m)
    (T : Finset (Fin m)) : Prop :=
  G.SpanningTree T ∧ ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    ((G.cut T S).card : ℝ) ≤ C / (k : ℝ) * (G.cut Finset.univ S).card

def ExplicitInput.encodeEdges (x : ExplicitInput) (edges : List (Fin x.m)) : List Bool :=
  edges.flatMap (fun e => CurrentKS.encodeNat e.val)

def BinaryInput.encodeEdges (x : BinaryInput) (edges : List x.Edge) : List Bool :=
  edges.flatMap (fun e => CurrentKS.encodeNat e.1.val ++ CurrentKS.encodeNat e.2.val)

noncomputable def BinaryInput.selected (x : BinaryInput) (edges : List x.Edge) :
    Finset (Fin (Fintype.card x.Edge)) := edges.toFinset.map x.edgeEquiv.toEmbedding

def TreeOutput (C : ℝ) : Input → List Bool → Prop
  | .explicit x, bits => ∃ edges : List (Fin x.m), edges.Nodup ∧
      bits = x.encodeEdges edges ∧ ThinTree C x.k x.graph edges.toFinset
  | .binary x, bits => ∃ edges : List x.Edge, edges.Nodup ∧
      bits = x.encodeEdges edges ∧ ThinTree C x.k x.graph (x.selected edges)

def GoodOutput (C : ℝ) (x : Input) (bits : List Bool) : Prop :=
  TreeOutput C x bits ∧ (x.n = 1 → bits = [])

def AlgorithmicStrongThinTrees : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ M : CurrentKS.Machine, ∃ a degree : ℕ, 0 < a ∧
    ∀ x : Input, Valid x →
      let result := M.run x.encode (a * (x.length + 1) ^ degree)
      result.state = none ∧ GoodOutput C x (result.stacks M.outputStack)

end AlgorithmicThinTrees

namespace AlgorithmicThinTrees

def algorithmic_strong_thin_trees_statement : Prop :=
  AlgorithmicStrongThinTrees

end AlgorithmicThinTrees

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees_statement

end Problem

/- Formalization scope, from lean/docs/174.md: The strong thin-tree conjecture asks for spanning trees that cross every cut sparsely relative to the original graph. The formalized result gives one absolute constant $C>0$ such that every finite loopless $k$-edge-connected multigraph with at least two vertices has a spanning tree crossing each nontrivial cut at most $(C/k)$ times the original cut size. Parallel edges remain distinct. No numerical value of $C$ or construction algorithm is asserted. The strong thin-tree problem asks for a spanning tree that crosses every cut sparsely relative to the original graph. The formalization gives one deterministic polynomial-time algorithm and an absolute constant $C>0$ such that a finite $k$-edge-connected loopless multigraph yields a spanning tree using at most a $C/k$ fraction of the edges of every cut. The input may encode parallel-edge multiplicities in binary, and the running time is polynomial in that binary input length. -/
