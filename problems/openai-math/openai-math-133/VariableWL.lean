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

- problem_id: VariableWL
- collection: openai-math
- question_id: openai-math:133
- source: openai-math
- source_locator: lean/ComparatorChallenges/VariableWL.lean#OAI.VariableWL.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves unconditional $`n^{\Omega(k)}`$ deterministic time lower bounds for joint and separate k-dimensional Weisfeiler–Leman equivalence, for sufficiently large fixed k in the specified sequential adjacency-matrix models. With dimension as input, joint equivalence is EXPTIME-complete even on subcubic graphs; deciding whether refinement identifies a graph is also EXPTIME-complete. ([Lean](lean/docs/133.md)) For k ≥ 4, we construct two uncolored graphs that are k-dimensional Weisfeiler–Leman equivalent exactly when a prescribed finite-domain choice system has no compatible choice. The system has $`k+1`$ domains for joint refinement and k for separate-coordinate refinement. A successful choice is detected after two joint rounds or one separate round. Applied to sparse satisfiability, the reduction gives fixed-dimension $`n^{\Omega(k)}`$ time exclusions under positive-rate ETH, even for deciding equality of these early histograms. We prove that deciding whether Weisfeiler–Leman refinement of an input dimension identifies a given graph is EXPTIME-complete. The input is a nonempty finite simple uncolored graph in adjacency-matrix form and a positive binary-encoded dimension. Identification quantifies over every comparison graph. For every sufficiently large fixed k, deciding whether two n-vertex graphs are k-Weisfeiler–Leman equivalent requires $`n^{\Omega(k)}`$ deterministic sequential time in the worst case. The bound holds at every sufficiently large graph order, even for simple connected uncolored graphs of diameter at most two, without a complexity assumption. Inputs are explicit adjacency matrices; the models are multitape Turing machines and sequential logarithmic-word RAMs with fixed polynomial-bit-time instructions. Both joint and separate replacement conventions are covered. Deciding joint-update k-dimensional Weisfeiler–Leman equivalence is $`\mathsf{EXPTIME}`$-complete when the two graphs are given by explicit adjacency matrices and k ≥ 2 is encoded in binary. The result holds even for connected simple uncolored graphs of equal positive order and maximum degree at most three.
- notes: OpenAI math result family 133, The computational complexity of Weisfeiler–Leman refinement -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/133.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.VariableWL.main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.VariableWL.Completeness
- source_papers: preprints/Parity-lifts-and-bounded-treewidth-witnesses-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf preprints/The-complexity-of-identifying-a-graph-by-Weisfeiler-Leman-refinement-September-25-2026/paper.pdf preprints/Unconditional-time-lower-bounds-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf preprints/Variable-dimension-Weisfeiler-Leman-equivalence-on-general-and-subcubic-graphs-September-25-2026/paper.pdf
- source_scope_note: lean/docs/133.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace VariableWL

abbrev Word := List Bool

inductive Motion where
  | left | stay | right
  deriving DecidableEq

def Motion.displacement : Motion → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure Machine where
  states : ℕ
  workSymbols : ℕ
  extraTapes : ℕ
  transition : Fin (states + 1) →
    (Fin (extraTapes + 1) → Fin (workSymbols + 3)) →
    Option (Fin (states + 1) ×
      (Fin (extraTapes + 1) → Fin (workSymbols + 3) × Motion))

structure Configuration (M : Machine) where
  control : Fin (M.states + 1)
  heads : Fin (M.extraTapes + 1) → ℤ
  cells : Fin (M.extraTapes + 1) → ℤ → Fin (M.workSymbols + 3)

def wordCells (a : ℕ) (w : Word) (i : ℤ) : Fin (a + 3) :=
  if 0 ≤ i then
    match w[i.toNat]? with
    | none => 0
    | some false => 1
    | some true => 2
  else 0

def initial (M : Machine) (w : Word) : Configuration M where
  control := 0
  heads := fun _ => 0
  cells := fun j => if j = 0 then wordCells M.workSymbols w else fun _ => 0

def scanned {M : Machine} (c : Configuration M) :
    Fin (M.extraTapes + 1) → Fin (M.workSymbols + 3) :=
  fun j => c.cells j (c.heads j)

def step (M : Machine) (c : Configuration M) : Option (Configuration M) :=
  (M.transition c.control (scanned c)).map fun data =>
    { control := data.1
      heads := fun j => c.heads j + (data.2 j).2.displacement
      cells := fun j i => if i = c.heads j then (data.2 j).1 else c.cells j i }

def run (M : Machine) (w : Word) : ℕ → Configuration M
  | 0 => initial M w
  | n + 1 => (step M (run M w n)).getD (run M w n)

def OutputsWithin (M : Machine) (w out : Word) (bound : ℕ) : Prop :=
  ∃ t ≤ bound, step M (run M w t) = none ∧
    (run M w t).cells 0 = wordCells M.workSymbols out

abbrev Language := Set Word

def InEXPTIME (L : Language) : Prop :=
  ∃ M : Machine, ∃ c d : ℕ, ∀ w : Word,
    ∃ b : Bool, (b = true ↔ w ∈ L) ∧
      OutputsWithin M w [b] (2 ^ (c * (w.length + 1) ^ d))

def PolytimeReduces (L R : Language) : Prop :=
  ∃ M : Machine, ∃ c d : ℕ, ∀ w : Word,
    ∃ out : Word, OutputsWithin M w out (c * (w.length + 1) ^ d) ∧
      (w ∈ L ↔ out ∈ R)

def EXPTIMEComplete (L : Language) : Prop :=
  InEXPTIME L ∧ ∀ R : Language, InEXPTIME R → PolytimeReduces R L

structure Graph where
  order : ℕ
  graph : SimpleGraph (Fin order)

abbrev Tuple (G : Graph) (k : ℕ) := Fin k → Fin G.order

def Color (k : ℕ) : ℕ → Type
  | 0 => Fin k → Fin k → Bool × Bool
  | s + 1 => Color k s × Multiset (Fin k → Color k s)

noncomputable def color (G : Graph) (k : ℕ) : (s : ℕ) → Tuple G k → Color k s
  | 0, v => by
      classical
      exact fun i j => (decide (v i = v j), decide (G.graph.Adj (v i) (v j)))
  | s + 1, v => (color G k s v,
      Finset.univ.val.map (fun z => fun i => color G k s (Function.update v i z)))

noncomputable def histogram (G : Graph) (k s : ℕ) : Multiset (Color k s) :=
  Finset.univ.val.map (color G k s)

def Equivalent (G H : Graph) (k : ℕ) : Prop :=
  ∀ s : ℕ, histogram G k s = histogram H k s

def integerCode (n : ℕ) : Word :=
  List.replicate (Nat.bits n).length true ++ [false] ++ Nat.bits n

noncomputable def graphCode (G : Graph) : Word := by
  classical
  exact integerCode G.order ++
    (List.ofFn fun i : Fin G.order =>
      List.ofFn fun j : Fin G.order => decide (G.graph.Adj i j)).flatten

noncomputable def pairCode (G H : Graph) (k : ℕ) : Word :=
  graphCode G ++ graphCode H ++ integerCode k

def WL : Language :=
  { w | ∃ G H : Graph, ∃ k : ℕ, w = pairCode G H k ∧ 2 ≤ k ∧ Equivalent G H k }

noncomputable def Subcubic (G : Graph) : Prop := by
  classical
  exact ∀ v : Fin G.order, G.graph.degree v ≤ 3

def SubWL : Language :=
  { w | ∃ G H : Graph, ∃ k : ℕ, w = pairCode G H k ∧ 2 ≤ k ∧
    0 < G.order ∧ G.order = H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
    Subcubic G ∧ Subcubic H ∧ Equivalent G H k }

def main_statement : Prop :=
  EXPTIMEComplete WL ∧ EXPTIMEComplete SubWL

end VariableWL

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.VariableWL.main_statement

end Problem

/- Formalization scope, from lean/docs/133.md: The formalization gives the paper's parity-lift graph construction for every Weisfeiler–Leman dimension $k\ge4$, under both joint and separate conventions. From a finite choice system it constructs two equal-size uncolored graphs that are Weisfeiler–Leman equivalent exactly when the system has no successful compatible choice. The same equivalence holds for the pure variant. A successful choice is detected by the specified early round: round two in the joint convention and round one in the separate convention. The graph-size bound is linear in the choice-system size with a factor depending on $k$. The paper's conditional running-time exclusions are outside these selected construction statements. The formalization proves that deciding whether Weisfeiler–Leman refinement of a supplied dimension identifies a graph is EXPTIME-complete under polynomial-time many-one reductions. The input is a nonempty finite simple uncolored graph encoded by its adjacency matrix together with a positive binary-encoded dimension. Identification quantifies over every comparison graph, and the statement includes both the exponential-time upper bound and hardness. The formalization proves an unconditional deterministic time lower bound for deciding $k$-dimensional Weisfeiler–Leman equivalence. For every sufficiently large fixed $k$, every deciding algorithm in the stated multitape Turing-machine or sequential logarithmic-word RAM model requires at least $n^{ck}$ worst-case time for all sufficiently large graph orders $n$, for one absolute $c>0$. The bound covers both joint and separate replacement conventions and remains valid for explicit adjacency-matrix inputs restricted to simple connected uncolored graphs of diameter at most two. The formalization proves EXPTIME-completeness of deciding joint-update $k$-dimensional Weisfeiler–Leman equivalence when $k\ge2$ is part of the input in binary and the graphs are encoded by explicit adjacency matrices. It proves both the general result and the restriction to connected simple uncolored graphs of equal positive order and maximum degree at most three. Completeness uses polynomial-time many-one reductions. -/
