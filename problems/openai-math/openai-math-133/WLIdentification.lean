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

- problem_id: WLIdentification
- collection: openai-math
- question_id: openai-math:133
- source: openai-math
- source_locator: lean/ComparatorChallenges/WLIdentification.lean#OAI.WLIdentification.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves unconditional $`n^{\Omega(k)}`$ deterministic time lower bounds for joint and separate k-dimensional Weisfeiler–Leman equivalence, for sufficiently large fixed k in the specified sequential adjacency-matrix models. With dimension as input, joint equivalence is EXPTIME-complete even on subcubic graphs; deciding whether refinement identifies a graph is also EXPTIME-complete. ([Lean](lean/docs/133.md)) For k ≥ 4, we construct two uncolored graphs that are k-dimensional Weisfeiler–Leman equivalent exactly when a prescribed finite-domain choice system has no compatible choice. The system has $`k+1`$ domains for joint refinement and k for separate-coordinate refinement. A successful choice is detected after two joint rounds or one separate round. Applied to sparse satisfiability, the reduction gives fixed-dimension $`n^{\Omega(k)}`$ time exclusions under positive-rate ETH, even for deciding equality of these early histograms. We prove that deciding whether Weisfeiler–Leman refinement of an input dimension identifies a given graph is EXPTIME-complete. The input is a nonempty finite simple uncolored graph in adjacency-matrix form and a positive binary-encoded dimension. Identification quantifies over every comparison graph. For every sufficiently large fixed k, deciding whether two n-vertex graphs are k-Weisfeiler–Leman equivalent requires $`n^{\Omega(k)}`$ deterministic sequential time in the worst case. The bound holds at every sufficiently large graph order, even for simple connected uncolored graphs of diameter at most two, without a complexity assumption. Inputs are explicit adjacency matrices; the models are multitape Turing machines and sequential logarithmic-word RAMs with fixed polynomial-bit-time instructions. Both joint and separate replacement conventions are covered. Deciding joint-update k-dimensional Weisfeiler–Leman equivalence is $`\mathsf{EXPTIME}`$-complete when the two graphs are given by explicit adjacency matrices and k ≥ 2 is encoded in binary. The result holds even for connected simple uncolored graphs of equal positive order and maximum degree at most three.
- notes: OpenAI math result family 133, The computational complexity of Weisfeiler–Leman refinement -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/133.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.WLIdentification.main
- source_theorem_count: 1
- source_solution_module: OAI.Computability.WLIdentification.Main
- source_papers: preprints/Parity-lifts-and-bounded-treewidth-witnesses-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf preprints/The-complexity-of-identifying-a-graph-by-Weisfeiler-Leman-refinement-September-25-2026/paper.pdf preprints/Unconditional-time-lower-bounds-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf preprints/Variable-dimension-Weisfeiler-Leman-equivalence-on-general-and-subcubic-graphs-September-25-2026/paper.pdf
- source_scope_note: lean/docs/133.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace WLIdentification

structure Graph where
  order : ℕ
  edge : Fin order → Fin order → Bool
  symmetric : ∀ u v, edge u v = edge v u
  loopless : ∀ u, edge u u = false

def Isomorphic (G H : Graph) : Prop :=
  ∃ e : Fin G.order ≃ Fin H.order, ∀ u v, G.edge u v = H.edge (e u) (e v)

/-- Colors retain their full history, and hence are shared between graphs. -/
def NeighborColor : ℕ → Type
  | 0 => Unit
  | s + 1 => NeighborColor s × Multiset (NeighborColor s)

def neighborColor (G : Graph) : (s : ℕ) → Fin G.order → NeighborColor s
  | 0, _ => ()
  | s + 1, v => (neighborColor G s v,
      (Finset.univ.filter (fun w => G.edge v w = true)).val.map (neighborColor G s))

def neighborHistogram (G : Graph) (s : ℕ) : Multiset (NeighborColor s) :=
  Finset.univ.val.map (neighborColor G s)

def TupleColor (k : ℕ) : ℕ → Type
  | 0 => (Fin k → Fin k → Bool) × (Fin k → Fin k → Bool)
  | s + 1 => TupleColor k s × Multiset (Fin k → TupleColor k s)

/-- Joint update: one multiset of whole replacement vectors, not independent marginals. -/
def tupleColor (G : Graph) (k : ℕ) : (s : ℕ) → (Fin k → Fin G.order) → TupleColor k s
  | 0, v => (fun i j => decide (v i = v j), fun i j => G.edge (v i) (v j))
  | s + 1, v => (tupleColor G k s v,
      Finset.univ.val.map (fun z => fun i => tupleColor G k s (Function.update v i z)))

def tupleHistogram (G : Graph) (k s : ℕ) : Multiset (TupleColor k s) :=
  Finset.univ.val.map (tupleColor G k s)

def Equivalent (k : ℕ) (G H : Graph) : Prop :=
  if k = 1 then ∀ s, neighborHistogram G s = neighborHistogram H s
  else ∀ s, tupleHistogram G k s = tupleHistogram H k s

/-- There is no restriction to mates from a graph construction or to a selected order. -/
def Identifies (k : ℕ) (G : Graph) : Prop :=
  ∀ H : Graph, Equivalent k G H → Isomorphic G H

/-- The infimum of the positive identifying dimensions; this set is nonempty for finite G. -/
noncomputable def WLdim (G : Graph) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ Identifies k G}

abbrev Word := List Bool
abbrev BinaryLanguage := Set Word

def binaryValue (bits : Word) : ℕ :=
  bits.foldl (fun z b => 2 * z + if b then 1 else 0) 0

def matrixWord (G : Graph) : Word :=
  (List.ofFn (fun i : Fin G.order => List.ofFn (G.edge i))).flatten

/-- Unary order header, row-major binary matrix, then most-significant-first binary k. -/
def inputWord (G : Graph) (bits : Word) : Word :=
  List.replicate G.order true ++ [false] ++ matrixWord G ++ bits

/-- A malformed word is rejected: membership requires a valid nonempty simple matrix and k>0. -/
def dimensionLanguage : BinaryLanguage :=
  {w | ∃ (G : Graph) (bits : Word),
    0 < G.order ∧ (∃ tail, bits = true :: tail) ∧ 0 < binaryValue bits ∧
    w = inputWord G bits ∧ WLdim G ≤ binaryValue bits}

/- The deterministic local machine model is explicit; no oracle or arbitrary
   state-transition on whole inputs is included. Both alphabets are fixed finite
   types for each machine. Extra symbols and states allow arbitrary finite tables. -/
inductive Move where
  | left | stay | right
  deriving DecidableEq

def Move.displacement : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure Machine where
  extraSymbols : ℕ
  extraStates : ℕ
  transition : Fin (extraStates + 3) → Fin (extraSymbols + 3) →
    Fin (extraStates + 3) × Fin (extraSymbols + 3) × Move

structure Configuration (M : Machine) where
  state : Fin (M.extraStates + 3)
  head : ℤ
  tape : ℤ → Fin (M.extraSymbols + 3)

def inputSymbol (M : Machine) (b : Bool) : Fin (M.extraSymbols + 3) :=
  if b then 2 else 1

def initial (M : Machine) (w : Word) : Configuration M where
  state := 0
  head := 0
  tape z := if 0 ≤ z then (w[z.toNat]?).elim 0 (inputSymbol M) else 0

def Halted {M : Machine} (c : Configuration M) : Prop :=
  c.state = 1 ∨ c.state = 2

/-- One read/write/head-movement transition. A halted configuration is frozen. -/
def step (M : Machine) (c : Configuration M) : Configuration M :=
  if c.state = 1 ∨ c.state = 2 then c else
    let t := M.transition c.state (c.tape c.head)
    { state := t.1, head := c.head + t.2.2.displacement,
      tape := Function.update c.tape c.head t.2.1 }

def run (M : Machine) (w : Word) (t : ℕ) : Configuration M :=
  (step M)^[t] (initial M w)

/-- Output is the binary word beginning at origin and ending at its first blank. -/
def Output {M : Machine} (c : Configuration M) (w : Word) : Prop :=
  (∀ i : Fin w.length, c.tape (i.val : ℤ) = inputSymbol M w[i]) ∧
    c.tape (w.length : ℤ) = 0

/-- Uniform genuine executions on every bit word, including malformed graph words. -/
def DecidesWithin (M : Machine) (L : BinaryLanguage) (bound : ℕ → ℕ) : Prop :=
  ∀ w, ∃ t ≤ bound w.length, Halted (run M w t) ∧ ((run M w t).state = 1 ↔ w ∈ L)

def InEXPTIME (L : BinaryLanguage) : Prop :=
  ∃ (M : Machine) (C d : ℕ),
    DecidesWithin M L (fun n => 2 ^ (C * (n + 1) ^ d))

def ComputesWithin (M : Machine) (f : Word → Word) (bound : ℕ → ℕ) : Prop :=
  ∀ w, ∃ t ≤ bound w.length, (run M w t).state = 1 ∧ Output (run M w t) (f w)

def PolytimeManyOne (L S : BinaryLanguage) : Prop :=
  ∃ (f : Word → Word) (M : Machine) (C d : ℕ),
    ComputesWithin M f (fun n => C * (n + 1) ^ d) ∧ ∀ w, w ∈ L ↔ f w ∈ S

def EXPTIMEComplete (S : BinaryLanguage) : Prop :=
  InEXPTIME S ∧ ∀ L : BinaryLanguage, InEXPTIME L → PolytimeManyOne L S

def main_statement : Prop :=
  EXPTIMEComplete dimensionLanguage

end WLIdentification

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.WLIdentification.main_statement

end Problem

/- Formalization scope, from lean/docs/133.md: The formalization gives the paper's parity-lift graph construction for every Weisfeiler–Leman dimension $k\ge4$, under both joint and separate conventions. From a finite choice system it constructs two equal-size uncolored graphs that are Weisfeiler–Leman equivalent exactly when the system has no successful compatible choice. The same equivalence holds for the pure variant. A successful choice is detected by the specified early round: round two in the joint convention and round one in the separate convention. The graph-size bound is linear in the choice-system size with a factor depending on $k$. The paper's conditional running-time exclusions are outside these selected construction statements. The formalization proves that deciding whether Weisfeiler–Leman refinement of a supplied dimension identifies a graph is EXPTIME-complete under polynomial-time many-one reductions. The input is a nonempty finite simple uncolored graph encoded by its adjacency matrix together with a positive binary-encoded dimension. Identification quantifies over every comparison graph, and the statement includes both the exponential-time upper bound and hardness. The formalization proves an unconditional deterministic time lower bound for deciding $k$-dimensional Weisfeiler–Leman equivalence. For every sufficiently large fixed $k$, every deciding algorithm in the stated multitape Turing-machine or sequential logarithmic-word RAM model requires at least $n^{ck}$ worst-case time for all sufficiently large graph orders $n$, for one absolute $c>0$. The bound covers both joint and separate replacement conventions and remains valid for explicit adjacency-matrix inputs restricted to simple connected uncolored graphs of diameter at most two. The formalization proves EXPTIME-completeness of deciding joint-update $k$-dimensional Weisfeiler–Leman equivalence when $k\ge2$ is part of the input in binary and the graphs are encoded by explicit adjacency matrices. It proves both the general result and the restriction to connected simple uncolored graphs of equal positive order and maximum degree at most three. Completeness uses polynomial-time many-one reductions. -/
