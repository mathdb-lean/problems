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

- problem_id: StrongThinTree
- collection: openai-math
- question_id: openai-math:174
- source: openai-math
- source_locator: lean/ComparatorChallenges/StrongThinTree.lean#OAI.StrongThinTree.strongThinTree
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the strong thin-tree conjecture constructively. Every finite loopless k-edge-connected multigraph on at least two vertices has a spanning tree containing at most a universal $`C/k`$ fraction of the edges of every cut. Such a tree can be found deterministically in polynomial time, even with binary-encoded parallel-edge multiplicities. ([Lean](lean/docs/174.md)) We prove that every finite loopless k-edge-connected multigraph on at least two vertices, with k ≥ 1, has a spanning tree meeting each cut in at most $`C/k`$ times the size of the cut, where C is a universal constant. This resolves the strong thin tree conjecture. We give a deterministic polynomial-time construction of strong thin trees. Given a finite k-edge-connected loopless multigraph on at least one vertex, the algorithm constructs a spanning tree meeting every cut in at most a $`C/k`$ fraction of its edges, for a universal constant C. The running time is polynomial in the binary input length, including when parallel-edge multiplicities are encoded in binary.
- notes: OpenAI math result family 174, Deterministic construction of strong thin spanning trees -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/174.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.StrongThinTree.strongThinTree
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.ThinTrees.Main
- source_main_result: OAI.StrongThinTree.strongThinTree
- source_papers: preprints/The-strong-thin-tree-conjecture-September-23-2026/paper.pdf preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf
- source_scope_note: lean/docs/174.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

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

def MainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (n m : ℕ), 2 ≤ n →
    ∀ G : MultiGraph n m, G.EdgeConnected k →
      ∃ T : Finset (Fin m), G.SpanningTree T ∧
        ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
          ((G.cut T S).card : ℝ) ≤ (C / (k : ℝ)) * (G.cut Finset.univ S).card

def strongThinTree_statement : Prop :=
  MainStatement

end StrongThinTree

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.StrongThinTree.strongThinTree_statement

end Problem

/- Formalization scope, from lean/docs/174.md: The strong thin-tree conjecture asks for spanning trees that cross every cut sparsely relative to the original graph. The formalized result gives one absolute constant $C>0$ such that every finite loopless $k$-edge-connected multigraph with at least two vertices has a spanning tree crossing each nontrivial cut at most $(C/k)$ times the original cut size. Parallel edges remain distinct. No numerical value of $C$ or construction algorithm is asserted. The strong thin-tree problem asks for a spanning tree that crosses every cut sparsely relative to the original graph. The formalization gives one deterministic polynomial-time algorithm and an absolute constant $C>0$ such that a finite $k$-edge-connected loopless multigraph yields a spanning tree using at most a $C/k$ fraction of the edges of every cut. The input may encode parallel-edge multiplicities in binary, and the running time is polynomial in that binary input length. -/
