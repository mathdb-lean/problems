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

- problem_id: CommonBasesFPRAS
- collection: openai-math
- question_id: openai-math:114
- source: openai-math
- source_locator: lean/ComparatorChallenges/CommonBasesFPRAS.lean#OAI.common_bases_fpras
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives a fully polynomial randomized approximation scheme for counting common integer bases of two integral polymatroids of equal total rank, supplied by exact rank-value oracles. Capacities are binary-encoded, each integer vector counts once, and oracle calls and bit operations outside the oracles are polynomial on every execution. For matroids presented by independence oracles, the results also cover common independent sets of prescribed, unrestricted, or maximum cardinality, even when the ranks differ. ([Lean](lean/docs/114.md)) We give a fully polynomial randomized approximation scheme for counting the common bases of two arbitrary matroids of the same rank, supplied by independence oracles. The algorithm requires no explicit representation of either matroid and has polynomial bounds on both oracle calls and bit operations on every execution.
- notes: OpenAI math result family 114, Approximate counting of common integer polymatroid bases -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/114.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.common_bases_fpras
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.MatroidCounting.CommonBases
- source_main_result: OAI.common_bases_fpras
- source_papers: preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/main.pdf
- source_scope_note: lean/docs/114.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace CommonBasesFPRAS

abbrev IndependenceOracle (n : ℕ) := Bool → (Fin n → Bool) → Bool

def ExactOracles {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (O : IndependenceOracle n) : Prop :=
  ∀ (which : Bool) (A : Fin n → Bool),
    O which A = true ↔ (if which then M₂ else M₁).Indep {i | A i = true}

noncomputable def commonBaseCount {n : ℕ} (M₁ M₂ : Matroid (Fin n)) : ℕ :=
  Nat.card {A : Finset (Fin n) // M₁.IsBase (A : Set (Fin n)) ∧
    M₂.IsBase (A : Set (Fin n))}

inductive Instruction (k s : ℕ) where
  | push (register : Fin (k + 8)) (bit : Bool) (next : Fin (s + 1))
  | pop (register : Fin (k + 8)) (empty zero one : Fin (s + 1))
  | coin (zero one : Fin (s + 1))
  | query (which : Bool) (register : Fin (k + 8)) (no yes : Fin (s + 1))
  | halt

def Program (k s : ℕ) := Fin (s + 1) → Instruction k s

def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * binaryValue l

structure MachineConfig (k s : ℕ) where
  registers : Fin (k + 8) → List Bool
  control : Fin (s + 1)
  output : Option ℚ := none
  oracleCalls : ℕ := 0
  bitOperations : ℕ := 0

def inputLength (n r : ℕ) (ε δ : ℚ) : ℕ :=
  6 + n.bits.length + r.bits.length + ε.num.natAbs.bits.length + ε.den.bits.length +
    δ.num.natAbs.bits.length + δ.den.bits.length

def initialConfig (k s n r : ℕ) (ε δ : ℚ) : MachineConfig k s where
  registers := fun i => match i.val with
    | 0 => n.bits
    | 1 => r.bits
    | 2 => ε.num.natAbs.bits
    | 3 => ε.den.bits
    | 4 => δ.num.natAbs.bits
    | 5 => δ.den.bits
    | _ => []
  control := 0

def machineStep {k s n : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (randomBit : Bool) (c : MachineConfig k s) : MachineConfig k s :=
  if c.output.isSome then c else
  match P c.control with
  | .push i b next =>
    { c with
      registers := Function.update c.registers i (b :: c.registers i)
      control := next
      bitOperations := c.bitOperations + 1 }
  | .pop i empty zero one =>
    match c.registers i with
    | [] => { c with
      control := empty
      bitOperations := c.bitOperations + 1 }
    | b :: l =>
      { c with
      registers := Function.update c.registers i l
      control := if b then one else zero
      bitOperations := c.bitOperations + 1 }
  | .coin zero one =>
    { c with
      control := if randomBit then one else zero
      bitOperations := c.bitOperations + 1 }
  | .query which i no yes =>
    if (c.registers i).length = n then
      { c with
      control := if O which (fun j => (c.registers i)[j.val]?.getD false)
          then yes else no
      oracleCalls := c.oracleCalls + 1
      bitOperations := c.bitOperations + (c.registers i).length + n + 1 }
    else
      { c with
      output := some 0
      bitOperations := c.bitOperations + (c.registers i).length + n + 1 }
  | .halt =>
    { c with
      output := some ((binaryValue (c.registers ⟨6, by omega⟩) : ℚ) /
        (binaryValue (c.registers ⟨7, by omega⟩) : ℚ))
      bitOperations := c.bitOperations + (c.registers ⟨6, by omega⟩).length +
        (c.registers ⟨7, by omega⟩).length + 1 }

def execution {k s n : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) : ℕ → MachineConfig k s
  | 0 => c
  | t + 1 => machineStep P O (bits t) (execution P O c bits t)

def finiteBits {B : ℕ} (bits : Fin B → Bool) (t : ℕ) : Bool :=
  if h : t < B then bits ⟨t, h⟩ else false

def relativeAccuracy (ε : ℚ) (Z : ℕ) (z : ℚ) : Prop :=
  (1-ε)*(Z:ℚ)≤z ∧ z≤(1+ε)*(Z:ℚ)

def resourceBound (C d n r : ℕ) (ε δ : ℚ) : ℕ :=
  C * (1 + n + inputLength n r ε δ + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊) ^ d

def MainTheorem : Prop :=
  ∃ (k s : ℕ) (P : Program k s) (C d : ℕ), 0 < C ∧
    ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n)
      (ε δ : ℚ),
      M₁.E = Set.univ → M₂.E = Set.univ →
      M₁.eRank = (r : ℕ∞) → M₂.eRank = (r : ℕ∞) →
      ExactOracles M₁ M₂ O → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      let B := resourceBound C d n r ε δ
      let Z := commonBaseCount M₁ M₂
      (∀ bits : ℕ → Bool,
        let out := execution P O (initialConfig k s n r ε δ) bits B
        out.output.isSome ∧ out.oracleCalls ≤ B ∧ out.bitOperations ≤ B ∧
        ∀ z, out.output = some z → 0 ≤ z ∧ (Z = 0 → z = 0)) ∧
      (1 - δ) * (2 : ℚ) ^ B ≤
        (Nat.card {bits : Fin B → Bool //
          ∃ z, (execution P O (initialConfig k s n r ε δ) (finiteBits bits) B).output
            = some z ∧ relativeAccuracy ε Z z} : ℚ)

end CommonBasesFPRAS

def common_bases_fpras_statement : Prop :=
  CommonBasesFPRAS.MainTheorem

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.common_bases_fpras_statement

end Problem

/- Formalization scope, from lean/docs/114.md: The formalized result gives a fully polynomial randomized approximation scheme for the number of common bases of two equal-rank matroids on an enumerated finite ground set, using independence oracles. For rational $0<\varepsilon,\delta<1$, the nonnegative rational output has relative error at most $\varepsilon$ with probability at least $1-\delta$. A zero count produces zero on every execution. Oracle calls and bit operations have polynomial bounds on every random tape in the input size, $\varepsilon^{-1}$, and $\log(\delta^{-1})$. -/
