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

- problem_id: WeisfeilerLeman
- collection: openai-math
- question_id: openai-math:133
- source: openai-math
- source_locator: lean/ComparatorChallenges/WeisfeilerLeman.lean#OAI.WLTime.unconditional_time_lower_bound
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves unconditional $`n^{\Omega(k)}`$ deterministic time lower bounds for joint and separate k-dimensional Weisfeiler–Leman equivalence, for sufficiently large fixed k in the specified sequential adjacency-matrix models. With dimension as input, joint equivalence is EXPTIME-complete even on subcubic graphs; deciding whether refinement identifies a graph is also EXPTIME-complete. ([Lean](lean/docs/133.md)) For k ≥ 4, we construct two uncolored graphs that are k-dimensional Weisfeiler–Leman equivalent exactly when a prescribed finite-domain choice system has no compatible choice. The system has $`k+1`$ domains for joint refinement and k for separate-coordinate refinement. A successful choice is detected after two joint rounds or one separate round. Applied to sparse satisfiability, the reduction gives fixed-dimension $`n^{\Omega(k)}`$ time exclusions under positive-rate ETH, even for deciding equality of these early histograms. We prove that deciding whether Weisfeiler–Leman refinement of an input dimension identifies a given graph is EXPTIME-complete. The input is a nonempty finite simple uncolored graph in adjacency-matrix form and a positive binary-encoded dimension. Identification quantifies over every comparison graph. For every sufficiently large fixed k, deciding whether two n-vertex graphs are k-Weisfeiler–Leman equivalent requires $`n^{\Omega(k)}`$ deterministic sequential time in the worst case. The bound holds at every sufficiently large graph order, even for simple connected uncolored graphs of diameter at most two, without a complexity assumption. Inputs are explicit adjacency matrices; the models are multitape Turing machines and sequential logarithmic-word RAMs with fixed polynomial-bit-time instructions. Both joint and separate replacement conventions are covered. Deciding joint-update k-dimensional Weisfeiler–Leman equivalence is $`\mathsf{EXPTIME}`$-complete when the two graphs are given by explicit adjacency matrices and k ≥ 2 is encoded in binary. The result holds even for connected simple uncolored graphs of equal positive order and maximum degree at most three.
- notes: OpenAI math result family 133, The computational complexity of Weisfeiler–Leman refinement -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/133.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.WLTime.unconditional_time_lower_bound
- source_theorem_count: 1
- source_solution_module: OAI.Computability.WeisfeilerLeman.Main
- source_papers: preprints/Parity-lifts-and-bounded-treewidth-witnesses-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf preprints/The-complexity-of-identifying-a-graph-by-Weisfeiler-Leman-refinement-September-25-2026/paper.pdf preprints/Unconditional-time-lower-bounds-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf preprints/Variable-dimension-Weisfeiler-Leman-equivalence-on-general-and-subcubic-graphs-September-25-2026/paper.pdf
- source_scope_note: lean/docs/133.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace WLTime

inductive Convention where
  | joint | separate
  deriving DecidableEq

def Graph (n : ℕ) :=
  { a : Fin n → Fin n → Bool //
    (∀ x y, a x y = a y x) ∧ (∀ x, a x x = false) }

namespace Graph

def adj {n : ℕ} (G : Graph n) : Fin n → Fin n → Bool := G.val

def diameterTwo {n : ℕ} (G : Graph n) : Prop :=
  0 < n ∧ ∀ x y, x = y ∨ G.adj x y = true ∨
    ∃ z, G.adj x z = true ∧ G.adj z y = true

noncomputable instance (n : ℕ) : Fintype (Graph n) := by
  classical
  unfold Graph
  infer_instance

end Graph

abbrev AtomicColor (k : ℕ) :=
  (Fin k → Fin k → Bool) × (Fin k → Fin k → Bool)

def Color (c : Convention) (k : ℕ) : ℕ → Type
  | 0 => AtomicColor k
  | t + 1 => match c with
    | .joint => Color c k t × Multiset (Fin k → Color c k t)
    | .separate => Color c k t × (Fin k → Multiset (Color c k t))

noncomputable def tupleColor {n : ℕ} (c : Convention) (k : ℕ) (G : Graph n) :
    (t : ℕ) → (Fin k → Fin n) → Color c k t
  | 0, v => (fun i j => decide (v i = v j), fun i j => G.adj (v i) (v j))
  | t + 1, v => match c with
    | .joint => (tupleColor .joint k G t v,
        Finset.univ.val.map (fun z => fun i =>
          tupleColor .joint k G t (Function.update v i z)))
    | .separate => (tupleColor .separate k G t v,
        fun i => Finset.univ.val.map (fun z =>
          tupleColor .separate k G t (Function.update v i z)))

noncomputable def histogram {n : ℕ} (c : Convention) (k : ℕ) (G : Graph n)
    (t : ℕ) : Multiset (Color c k t) :=
  Finset.univ.val.map (tupleColor c k G t)

def Equivalent {n : ℕ} (c : Convention) (k : ℕ) (G H : Graph n) : Prop :=
  ∀ t, histogram c k G t = histogram c k H t

def encodeNat (n : ℕ) : List Bool :=
  let bits := (Nat.digits 2 n).map (fun b => decide (b = 1))
  List.replicate bits.length true ++ [false] ++ bits

def matrixBits {n : ℕ} (G : Graph n) : List Bool :=
  (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => G.adj i j).flatten

def encodePair {n : ℕ} (G H : Graph n) : List Bool :=
  encodeNat n ++ matrixBits G ++ matrixBits H

inductive Move where
  | left | stay | right
  deriving DecidableEq

def Move.displacement : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure TM where
  tapes : ℕ
  states : ℕ
  symbols : ℕ
  tapes_pos : 0 < tapes
  states_ge : 3 ≤ states
  symbols_ge : 3 ≤ symbols
  transition : Fin states → (Fin tapes → Fin symbols) →
    Fin states × (Fin tapes → Fin symbols) × (Fin tapes → Move)

namespace TM

structure Config (M : TM) where
  state : Fin M.states
  head : Fin M.tapes → ℤ
  tape : Fin M.tapes → ℤ → Fin M.symbols

def symbol (M : TM) (b : Bool) : Fin M.symbols :=
  if b then ⟨2, by have := M.symbols_ge; omega⟩ else
    ⟨1, by have := M.symbols_ge; omega⟩

def initial (M : TM) (w : List Bool) : M.Config where
  state := ⟨0, by have := M.states_ge; omega⟩
  head := fun _ => 0
  tape := fun a z => if a.val = 0 ∧ 0 ≤ z ∧ z.toNat < w.length then
    M.symbol (w.getD z.toNat false) else ⟨0, by have := M.symbols_ge; omega⟩

def halted (M : TM) (C : M.Config) : Prop := C.state.val = 1 ∨ C.state.val = 2

instance (M : TM) (C : M.Config) : Decidable (M.halted C) := inferInstanceAs
  (Decidable (C.state.val = 1 ∨ C.state.val = 2))

def step (M : TM) (C : M.Config) : M.Config :=
  if M.halted C then C else
  let tr := M.transition C.state (fun a => C.tape a (C.head a))
  { state := tr.1
    head := fun a => C.head a + (tr.2.2 a).displacement
    tape := fun a z => if z = C.head a then tr.2.1 a else C.tape a z }

def run (M : TM) (w : List Bool) (t : ℕ) : M.Config := M.step^[t] (M.initial w)

def halts (M : TM) (w : List Bool) : Prop := ∃ t, M.halted (M.run w t)

noncomputable def time (M : TM) (w : List Bool) : ℕ := by
  classical
  exact if h : M.halts w then Nat.find h else 0

def accepts (M : TM) (w : List Bool) : Prop :=
  ∃ t, (M.run w t).state.val = 1

def outputs (M : TM) (input output : List Bool) : Prop :=
  M.halts input ∧ ∀ i : Fin output.length,
    (M.run input (M.time input)).tape ⟨0, M.tapes_pos⟩ (i.val : ℤ) =
      M.symbol (output.get i)

end TM

abbrev Word (w : ℕ) := Fin (2 ^ w)

def wordBits {w : ℕ} (a : Word w) : List Bool :=
  List.ofFn (fun i : Fin w => a.val.testBit i.val)

def registerBits {R w : ℕ} (a : Fin R → Word w) : List Bool :=
  (List.ofFn fun i : Fin R => wordBits (a i)).flatten

structure WordOperation (R : ℕ) where
  apply : (w : ℕ) → (Fin R → Word w) → (Fin R → Word w)
  implementation : TM
  exponent : ℕ
  constant : ℕ
  computes : ∀ w a, implementation.outputs
    (encodeNat w ++ registerBits a) (registerBits (apply w a))
  cost : ∀ w (a : Fin R → Word w), implementation.time (encodeNat w ++ registerBits a) ≤
    constant * (w + 1) ^ exponent

inductive RAMInstruction (R P : ℕ) where
  | halt (answer : Bool)
  | jump (pc : Fin P)
  | compute (op : WordOperation R) (next : RAMInstruction R P)
  | load (dest addr : Fin R) (next : RAMInstruction R P)
  | store (addr src : Fin R) (next : RAMInstruction R P)
  | branchZero (reg : Fin R) (yes no : RAMInstruction R P)

structure WordWidth where
  bits : ℕ → ℕ
  positive : ∀ n, 0 < bits n
  bound : ℕ
  logarithmic : ∀ n, bits n ≤ bound * (Nat.log2 (n + 2) + 1)

structure RAM where
  registers : ℕ
  locations : ℕ
  locations_pos : 0 < locations
  width : WordWidth
  program : Fin locations → RAMInstruction registers locations
  input_fits : ∀ n (G H : Graph n),
    (encodePair G H).length ≤ width.bits n * 2 ^ width.bits n

namespace RAM

structure Config (A : RAM) (n : ℕ) where
  pc : Fin A.locations
  registers : Fin A.registers → Word (A.width.bits n)
  memory : Word (A.width.bits n) → Word (A.width.bits n)
  answer : Option Bool

def packedWord (w : ℕ) (input : List Bool) (a : Word w) : Word w :=
  ⟨(∑ i ∈ Finset.range w, if input.getD (w * a.val + i) false then 2 ^ i else 0)
      % (2 ^ w), Nat.mod_lt _ (by positivity)⟩

def initial (A : RAM) (n : ℕ) (w : List Bool) : A.Config n where
  pc := ⟨0, A.locations_pos⟩
  registers := fun _ => ⟨0, by positivity⟩
  memory := packedWord (A.width.bits n) w
  answer := none

def execute (A : RAM) {n : ℕ} :
    RAMInstruction A.registers A.locations → A.Config n → A.Config n
  | .halt b, C => { C with answer := some b }
  | .jump p, C => { C with pc := p }
  | .compute op next, C => A.execute next { C with
      registers := op.apply (A.width.bits n) C.registers }
  | .load dest addr next, C => A.execute next { C with
      registers := Function.update C.registers dest (C.memory (C.registers addr)) }
  | .store addr src next, C => A.execute next { C with
      memory := Function.update C.memory (C.registers addr) (C.registers src) }
  | .branchZero reg yes no, C =>
      if (C.registers reg).val = 0 then A.execute yes C else A.execute no C

def step (A : RAM) {n : ℕ} (C : A.Config n) : A.Config n :=
  match C.answer with
  | some _ => C
  | none => A.execute (A.program C.pc) C

def run (A : RAM) (n : ℕ) (w : List Bool) (t : ℕ) : A.Config n :=
  A.step^[t] (A.initial n w)

def halts (A : RAM) (n : ℕ) (w : List Bool) : Prop :=
  ∃ t, (A.run n w t).answer.isSome = true

noncomputable def time (A : RAM) (n : ℕ) (w : List Bool) : ℕ := by
  classical
  exact if h : A.halts n w then Nat.find h else 0

def accepts (A : RAM) (n : ℕ) (w : List Bool) : Prop :=
  ∃ t, (A.run n w t).answer = some true

end RAM

inductive Model where
  | turing (machine : TM)
  | ram (machine : RAM)

def Model.halts (A : Model) (n : ℕ) (w : List Bool) : Prop := match A with
  | .turing M => M.halts w
  | .ram M => M.halts n w

def Model.accepts (A : Model) (n : ℕ) (w : List Bool) : Prop := match A with
  | .turing M => M.accepts w
  | .ram M => M.accepts n w

noncomputable def Model.time (A : Model) (n : ℕ) (w : List Bool) : ℕ := match A with
  | .turing M => M.time w
  | .ram M => M.time n w

inductive InputClass where
  | unrestricted | diameterTwo
  deriving DecidableEq

def InputClass.contains (p : InputClass) {n : ℕ} (G H : Graph n) : Prop := match p with
  | .unrestricted => True
  | .diameterTwo => G.diameterTwo ∧ H.diameterTwo

def Decides (A : Model) (c : Convention) (k : ℕ) (p : InputClass) : Prop :=
  ∀ n (G H : Graph n), p.contains G H →
    A.halts n (encodePair G H) ∧
      (A.accepts n (encodePair G H) ↔ Equivalent c k G H)

noncomputable def worstTime (A : Model) (p : InputClass) (n : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup (fun pair : Graph n × Graph n =>
    if p.contains pair.1 pair.2 then A.time n (encodePair pair.1 pair.2) else 0)

def MainClaim : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∀ convention : Convention, ∀ p : InputClass, ∀ A : Model,
      Decides A convention k p → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (n : ℝ) ^ (c * (k : ℝ)) ≤ (worstTime A p n : ℝ)

end WLTime

def WLTime.unconditional_time_lower_bound_statement : Prop :=
  WLTime.MainClaim

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.WLTime.unconditional_time_lower_bound_statement

end Problem

/- Formalization scope, from lean/docs/133.md: The formalization gives the paper's parity-lift graph construction for every Weisfeiler–Leman dimension $k\ge4$, under both joint and separate conventions. From a finite choice system it constructs two equal-size uncolored graphs that are Weisfeiler–Leman equivalent exactly when the system has no successful compatible choice. The same equivalence holds for the pure variant. A successful choice is detected by the specified early round: round two in the joint convention and round one in the separate convention. The graph-size bound is linear in the choice-system size with a factor depending on $k$. The paper's conditional running-time exclusions are outside these selected construction statements. The formalization proves that deciding whether Weisfeiler–Leman refinement of a supplied dimension identifies a graph is EXPTIME-complete under polynomial-time many-one reductions. The input is a nonempty finite simple uncolored graph encoded by its adjacency matrix together with a positive binary-encoded dimension. Identification quantifies over every comparison graph, and the statement includes both the exponential-time upper bound and hardness. The formalization proves an unconditional deterministic time lower bound for deciding $k$-dimensional Weisfeiler–Leman equivalence. For every sufficiently large fixed $k$, every deciding algorithm in the stated multitape Turing-machine or sequential logarithmic-word RAM model requires at least $n^{ck}$ worst-case time for all sufficiently large graph orders $n$, for one absolute $c>0$. The bound covers both joint and separate replacement conventions and remains valid for explicit adjacency-matrix inputs restricted to simple connected uncolored graphs of diameter at most two. The formalization proves EXPTIME-completeness of deciding joint-update $k$-dimensional Weisfeiler–Leman equivalence when $k\ge2$ is part of the input in binary and the graphs are encoded by explicit adjacency matrices. It proves both the general result and the restriction to connected simple uncolored graphs of equal positive order and maximum degree at most three. Completeness uses polynomial-time many-one reductions. -/
