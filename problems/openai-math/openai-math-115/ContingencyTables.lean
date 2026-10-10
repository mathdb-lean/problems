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

- problem_id: ContingencyTables
- collection: openai-math
- question_id: openai-math:115
- source: openai-math
- source_locator: lean/ComparatorChallenges/ContingencyTables.lean#OAI.ContingencyTables.boundedSampling
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For nonnegative integer matrices with prescribed row and column sums, gives exact uniform sampling in expected polynomial bit time and almost-uniform sampling in worst-case polynomial bit time. The dimensions and binary-encoded margins are unrestricted. Also gives a fully polynomial randomized approximation scheme for counting such tables with arbitrary individual cell bounds, including structural zeros, with polynomial cost on every execution. ([Lean](lean/docs/115.md)) We give an exact uniform sampler for nonnegative integer contingency tables with arbitrary prescribed margins. It terminates almost surely and has expected bit complexity polynomial in both dimensions and the binary length of the margins. No positivity, balance, sparsity, or fixed-dimension assumption is required. We give a fully polynomial randomized approximation scheme for counting nonnegative integer matrices with prescribed row sums, column sums, and individual entry bounds. Both dimensions vary, all numerical data are encoded in binary, and zero bounds are allowed. The algorithm uses only unbiased random bits and has a polynomial bound on its bit operations on every execution.
- notes: OpenAI math result family 115, Sampling and counting contingency tables with arbitrary margins -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/115.md
- track: solved
- answer_shape: proof
- context_lemmas: entry_le_row entry_le_total alphabetSize_neZero
- source_theorem: OAI.ContingencyTables.boundedSampling OAI.ContingencyTables.exactSampling OAI.ContingencyTables.counting
- source_theorem_count: 3
- source_solution_module: OAI.Combinatorics.ContingencyTables.UnconditionalMain
- source_papers: preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/main.pdf
- source_scope_note: lean/docs/115.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace MatchingFPRAS

abbrev Symbol := Fin 8

/-- Binary numeral followed by a delimiter. Tape blank is 0; bits use 1 and 2. -/
def encodeNat (n : ℕ) : List Symbol :=
  (Nat.bits n).map (fun b => if b then 2 else 1) ++ [3]

def encodeInt (z : ℤ) : List Symbol :=
  (if z < 0 then [5] else [4]) ++ encodeNat z.natAbs

/-- A rational encoded by its reduced numerator and positive denominator. -/
def encodeRat (q : ℚ) : List Symbol := encodeInt q.num ++ encodeNat q.den

/-- A uniform randomized Post-Turing machine: a single finite transition table. -/
structure RandomMachine where
  states : ℕ
  transition : Fin (states + 1) → Symbol → Bool →
    Option (Fin (states + 1) × Turing.TM0.Stmt Symbol)

structure Configuration (A : RandomMachine) where
  state : Option (Fin (A.states + 1))
  tape : Turing.Tape Symbol

/-- A halted configuration is absorbing. Each nonhalting tick is exactly one
write or one move, or the detection of halt. -/
def tick (A : RandomMachine) (c : Configuration A) (bit : Bool) : Configuration A :=
  match c.state with
  | none => c
  | some s => match A.transition s c.tape.head bit with
    | none => ⟨none, c.tape⟩
    | some (s', action) =>
      ⟨some s', match action with
        | .move d => c.tape.move d
        | .write a => c.tape.write a⟩

def initial (A : RandomMachine) (input : List Symbol) : Configuration A :=
  ⟨some 0, Turing.Tape.mk₁ input⟩

/-- Bounded execution on a finite prefix of the random tape. -/
def run (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) : Configuration A :=
  (List.ofFn bits).foldl (tick A) (initial A input)

def Outputs (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) (q : ℚ) : Prop :=
  (run A input bits).state = none ∧
    (run A input bits).tape.right₀ = Turing.ListBlank.mk (encodeRat q)

end MatchingFPRAS

namespace ContingencyTables

open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

def HasMargins (X : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) : Prop :=
  (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j)

def Table (r : I → ℕ) (c : J → ℕ) := {X : I → J → ℕ // HasMargins X r c}

def BoundedTable (r : I → ℕ) (c : J → ℕ) (b : I → J → ℕ) :=
  {X : Table r c // ∀ i j, X.val i j ≤ b i j}

theorem entry_le_row {X : I → J → ℕ} {r : I → ℕ} {c : J → ℕ}
    (h : HasMargins X r c) (i : I) (j : J) : X i j ≤ r i := by
  rw [← h.1 i]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)

theorem entry_le_total {X : I → J → ℕ} {r : I → ℕ} {c : J → ℕ}
    (h : HasMargins X r c) (i : I) (j : J) : X i j ≤ ∑ i, r i :=
  (entry_le_row h i j).trans (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i))

instance table_finite (r : I → ℕ) (c : J → ℕ) : Finite (Table r c) := by
  let encode : Table r c → I → J → Fin ((∑ i, r i) + 1) :=
    fun X i j => ⟨X.val i j, Nat.lt_succ_of_le (entry_le_total X.property i j)⟩
  apply Finite.of_injective encode
  intro X Y h
  apply Subtype.ext
  funext i j
  exact congrArg Fin.val (congrFun (congrFun h i) j)

noncomputable instance table_fintype (r : I → ℕ) (c : J → ℕ) : Fintype (Table r c) :=
  Fintype.ofFinite _

noncomputable instance boundedTable_fintype (r : I → ℕ) (c : J → ℕ) (b : I → J → ℕ) :
    Fintype (BoundedTable r c b) := by
  classical
  unfold BoundedTable
  infer_instance

end ContingencyTables

namespace ContingencyTables.Algorithms

open scoped BigOperators
open Filter

abbrev Machine := MatchingFPRAS.RandomMachine
abbrev Symbol := MatchingFPRAS.Symbol

def encodeMatrix {m n : ℕ} (X : Fin m → Fin n → ℕ) : List Symbol :=
  ((List.ofFn fun i => (List.ofFn fun j => MatchingFPRAS.encodeNat (X i j)).flatten)).flatten

def encodeMargins {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) : List Symbol :=
  MatchingFPRAS.encodeNat m ++ MatchingFPRAS.encodeNat n ++
    (List.ofFn fun i => MatchingFPRAS.encodeNat (r i)).flatten ++
    (List.ofFn fun j => MatchingFPRAS.encodeNat (c j)).flatten

def encodeSamplingInput {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) : List Symbol :=
  encodeMargins r c ++ MatchingFPRAS.encodeNat k

def encodeCountingInput {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (ε δ : ℚ) : List Symbol :=
  encodeMargins r c ++ encodeMatrix b ++ MatchingFPRAS.encodeRat ε ++ MatchingFPRAS.encodeRat δ

/-- The tape alphabet has positive cardinality. -/
theorem alphabetSize_neZero : NeZero (8 : ℕ) := inferInstance

/-- A halted tape contains the row-major binary matrix encoding. -/
def OutputsTable (A : Machine) (input : List Symbol) {t m n : ℕ}
    (bits : Fin t → Bool) (X : Fin m → Fin n → ℕ) : Prop :=
  (MatchingFPRAS.run A input bits).state = none ∧
    @Turing.Tape.right₀ MatchingFPRAS.Symbol (@Fin.instInhabited 8 alphabetSize_neZero)
      (MatchingFPRAS.run A input bits).tape =
    @Turing.ListBlank.mk Symbol (@Fin.instInhabited 8 alphabetSize_neZero) (encodeMatrix X)

noncomputable def tableMass (A : Machine) (input : List Symbol) (t : ℕ)
    {m n : ℕ} (X : Fin m → Fin n → ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun bits : Fin t → Bool => OutputsTable A input bits X).card : ℝ) /
    (2 : ℝ) ^ t

noncomputable def haltMass (A : Machine) (input : List Symbol) (t : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun bits : Fin t → Bool =>
      (MatchingFPRAS.run A input bits).state = none).card : ℝ) / (2 : ℝ) ^ t

def samplingSize (n : ℕ) {m : ℕ} (r : Fin m → ℕ) (k : ℕ) : ℕ :=
  m + n + Nat.clog 2 ((∑ i, r i) + 1) + k + 1

/-- Paper 200-01, Theorem main(i): bounded runtime on every random tape
and total variation at most `2⁻ᵏ`, with freely varying dimensions. -/
def BoundedSamplingStatement : Prop :=
  ∃ (A : Machine) (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j → ∀ k : ℕ, 1 ≤ k →
        let input := encodeSamplingInput r c k
        let t := C * (samplingSize n r k) ^ d
        (∀ bits : Fin t → Bool, ∃ X : Table r c, OutputsTable A input bits X.val) ∧
        (∑ X : Table r c,
          |tableMass A input t X.val - (Fintype.card (Table r c) : ℝ)⁻¹|) / 2 ≤
            ((2 : ℝ) ^ k)⁻¹

/-- Paper 200-01, Theorem main(ii): every halted output is feasible, each
table has limiting mass `1/|Ω|`, termination has probability one, and the
expected number of bit operations is bounded by a uniform polynomial. -/
def ExactSamplingStatement : Prop :=
  ∃ (A : Machine) (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j →
        let input := encodeMargins r c
        let tail : ℕ → ℝ := fun t => 1 - haltMass A input t
        (∀ t (bits : Fin t → Bool), (MatchingFPRAS.run A input bits).state = none →
          ∃ X : Table r c, OutputsTable A input bits X.val) ∧
        (∀ X : Table r c, Tendsto (fun t => tableMass A input t X.val) atTop
          (nhds ((Fintype.card (Table r c) : ℝ)⁻¹))) ∧
        Tendsto (haltMass A input) atTop (nhds 1) ∧
        Summable tail ∧
        tsum tail ≤ C * (samplingSize n r 0) ^ d

noncomputable def count {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) : ℕ := Fintype.card (BoundedTable r c b)

def countingTime (C d : ℕ) {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (ε δ : ℚ) : ℕ :=
  C * ((encodeCountingInput r c b ε δ).length + ⌈ε⁻¹⌉₊ +
    Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ d

noncomputable def goodCountingTapes (A : Machine) {m n : ℕ}
    (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (ε δ : ℚ) (t : ℕ) : Finset (Fin t → Bool) := by
  classical
  exact Finset.univ.filter fun bits => ∃ q : ℚ,
    MatchingFPRAS.Outputs A (encodeCountingInput r c b ε δ) bits q ∧
      (1 - ε) * count r c b ≤ q ∧ q ≤ (1 + ε) * count r c b

/-- Paper 200-02, Theorem main. The input length includes the rational
accuracy parameters, and infeasible inputs always produce exactly zero. -/
def CountingStatement : Prop :=
  ∃ (A : Machine) (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ), 0 < m → 0 < n →
    ∀ (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j →
      ∀ ε δ : ℚ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        let input := encodeCountingInput r c b ε δ
        let t := countingTime C d r c b ε δ
        (∀ bits : Fin t → Bool, ∃ q : ℚ, 0 ≤ q ∧ MatchingFPRAS.Outputs A input bits q) ∧
        (count r c b = 0 → ∀ bits : Fin t → Bool, MatchingFPRAS.Outputs A input bits 0) ∧
        ((goodCountingTapes A r c b ε δ t).card : ℚ) / (2 : ℚ) ^ t ≥ 1 - δ

end ContingencyTables.Algorithms

namespace ContingencyTables

/-- An almost-uniform sampler with polynomial cost on every execution. -/
def boundedSampling_statement : Prop :=
  Algorithms.BoundedSamplingStatement

/-- Exact uniform sampling in polynomial expected bit time. -/
def exactSampling_statement : Prop :=
  Algorithms.ExactSamplingStatement

/-- A cell-bounded FPRAS, with zero output on every infeasible execution. -/
def counting_statement : Prop :=
  Algorithms.CountingStatement

end ContingencyTables

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ContingencyTables.boundedSampling_statement ∧
  _root_.OAI.ContingencyTables.exactSampling_statement ∧
  _root_.OAI.ContingencyTables.counting_statement

end Problem

/- Formalization scope, from lean/docs/115.md: The formalization gives an exact uniform sampler for nonnegative integer contingency tables with arbitrary prescribed row and column sums having equal totals. It terminates almost surely, every halted output is feasible, and each table has exactly the uniform limiting probability. Expected bit complexity is polynomial in the dimensions and the binary length of the margins. It also gives a sampler with a fixed polynomial time bound on every execution whose total-variation error is at most $2^{-k}$ for requested precision $k\ge1$. The same Comparator file includes the companion approximation scheme for counting tables with individual cell bounds. The formalization gives a fully polynomial randomized approximation scheme for counting nonnegative integer matrices with prescribed row sums, column sums, and individual entry bounds. Both dimensions may vary, the margins and bounds are binary encoded, and zero entry bounds are allowed. For rational $0<\varepsilon,\delta<1$, the algorithm returns a nonnegative estimate with relative error at most $\varepsilon$ with probability at least $1-\delta$, and returns zero on every execution when no table exists. The running time is polynomial in the encoded input size, $\varepsilon^{-1}$, and $\log(\delta^{-1})$ on every random tape. The same Comparator file also contains the companion sampling results for tables without cell bounds. -/
