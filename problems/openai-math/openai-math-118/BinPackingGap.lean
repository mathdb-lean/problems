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

- problem_id: BinPackingGap
- collection: openai-math
- question_id: openai-math:118
- source: openai-math
- source_locator: lean/ComparatorChallenges/BinPackingGap.lean#OAI.BinPackingGap.main_results
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves the modified integer round-up conjecture of Scheithauer and Terno: the integral bin-packing optimum can exceed its configuration linear-programming value by an arbitrarily large additive constant. Approximating the optimum within any fixed additive constant is also NP-hard, even when every item exceeds 1/6 and each bin holds at most five items. ([Lean](lean/docs/118.md)) We disprove the Modified Integer Round-Up Conjecture for bin packing by constructing instances with arbitrarily large additive gaps between the configuration-LP value and the integral optimum. We also prove that, for every fixed nonnegative integer c, distinguishing instances that fit in B bins from those requiring more than $`B+c`$ bins is NP-hard. Both results hold with rational item sizes greater than 1/6, so each bin contains at most five items.
- notes: OpenAI math result family 118, Bin packing and unbounded configuration-LP gaps -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/118.md
- track: solved
- answer_shape: proof
- context_lemmas: exists_packing positive capacityBound_spec count_lt_bound boundedCounts_injective den_pos
- source_theorem: OAI.BinPackingGap.main_results
- source_theorem_count: 1
- source_solution_module: OAI.Computability.BinPacking.Main
- source_main_result: OAI.BinPackingGap.main_results
- source_papers: preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf
- source_scope_note: lean/docs/118.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

end BinPackingGames.Foundations.Complexity

namespace BinPackingGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

end BinPackingGames.Foundations.Complexity.MachineFiniteAlphabet

namespace BinPackingGames.Foundations.Complexity.CookLevin

def pairBits (input : List Bool × List Bool) : List Bool :=
  encodeWord input.1.length ++ input.1 ++ input.2

structure NPVerifier where
  witnessBound : Polynomial Nat
  verify : (List Bool × List Bool) → Bool
  computation : Turing.TM2ComputableInPolyTime pairBits (fun bit => [bit]) verify
  finiteAlphabet : (k : computation.tm.K) → Fintype (computation.tm.Γ k)

def NPVerifier.Accepts (verifier : NPVerifier) (input : List Bool) : Prop :=
  ∃ witness : List Bool,
    witness.length ≤ verifier.witnessBound.eval input.length ∧
    verifier.verify (input, witness) = true

def InNP (language : List Bool → Prop) : Prop :=
  ∃ verifier : NPVerifier, ∀ input, language input ↔ verifier.Accepts input

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingCompleteness.BinaryEncoding

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

end BinPackingCompleteness.BinaryEncoding

namespace BinPackingGap

open scoped BigOperators

structure Instance where
  n : ℕ
  size : Fin n → ℚ
  size_pos : ∀ i, 0 < size i
  size_le_one : ∀ i, size i ≤ 1

namespace Instance

abbrev Item (I : Instance) := Fin I.n

end Instance

structure Packing (I : Instance) (b : ℕ) where
  assignment : I.Item → Fin b
  capacity : ∀ j, (∑ i, if assignment i = j then I.size i else 0) ≤ 1

def HasPacking (I : Instance) (b : ℕ) : Prop := Nonempty (Packing I b)

def singletonPacking (I : Instance) : Packing I I.n where
  assignment i := i
  capacity j := by
    have hsum : (∑ i, if i = j then I.size i else 0) = I.size j := by
      calc
        (∑ i, if i = j then I.size i else 0) =
            (if j = j then I.size j else 0) :=
          Finset.sum_eq_single j (fun i _ hij => ite_eq_right hij)
            (fun h => False.elim (h (Finset.mem_univ _)))
        _ = I.size j := ite_eq_left rfl
    rw [hsum]
    exact I.size_le_one j

theorem exists_packing (I : Instance) : ∃ b, HasPacking I b :=
  ⟨I.n, ⟨singletonPacking I⟩⟩

noncomputable def opt (I : Instance) : ℕ := by
  classical
  exact Nat.find (exists_packing I)

def IndividualConfiguration (I : Instance) :=
  {H : Finset I.Item // ∑ i ∈ H, I.size i ≤ 1}

noncomputable instance (I : Instance) : Fintype (IndividualConfiguration I) :=
  inferInstanceAs (Fintype {H : Finset I.Item // ∑ i ∈ H, I.size i ≤ 1})

def NumericalSize (I : Instance) := ↥(Finset.univ.image I.size)

instance (I : Instance) : Fintype (NumericalSize I) :=
  inferInstanceAs (Fintype ↥(Finset.univ.image I.size))

namespace NumericalSize

variable {I : Instance}

theorem positive (s : NumericalSize I) : 0 < s.val := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp s.property
  rw [← hi]
  exact I.size_pos i

def multiplicity (s : NumericalSize I) : ℕ :=
  (Finset.univ.filter fun i : I.Item => I.size i = s.val).card

def capacityBound (s : NumericalSize I) : ℕ :=
  Classical.choose (exists_nat_gt (1 / s.val))

theorem capacityBound_spec (s : NumericalSize I) : 1 / s.val < (s.capacityBound : ℚ) :=
  Classical.choose_spec (exists_nat_gt (1 / s.val))

end NumericalSize

def TypeConfiguration (I : Instance) :=
  {c : NumericalSize I → ℕ // ∑ s, s.val * (c s : ℚ) ≤ 1}

namespace TypeConfiguration

variable {I : Instance}

theorem count_lt_bound (c : TypeConfiguration I) (s : NumericalSize I) :
    c.val s < s.capacityBound := by
  have hterm : s.val * (c.val s : ℚ) ≤ ∑ t, t.val * (c.val t : ℚ) := by
    exact Finset.single_le_sum (fun t _ => mul_nonneg (le_of_lt t.positive) (Nat.cast_nonneg _))
      (Finset.mem_univ s)
  have hquot : (c.val s : ℚ) ≤ 1 / s.val := by
    apply (le_div_iff₀ s.positive).mpr
    simpa [mul_comm] using hterm.trans c.property
  have hlt := hquot.trans_lt s.capacityBound_spec
  exact_mod_cast hlt

def boundedCounts (c : TypeConfiguration I) : ∀ s : NumericalSize I, Fin s.capacityBound :=
  fun s => ⟨c.val s, c.count_lt_bound s⟩

theorem boundedCounts_injective :
    Function.Injective
      (boundedCounts : TypeConfiguration I → ∀ s : NumericalSize I, Fin s.capacityBound) := by
  intro c d h
  apply Subtype.ext
  funext s
  exact congrArg Fin.val (congrFun h s)

instance : Finite (TypeConfiguration I) := by
  classical
  exact Finite.of_injective boundedCounts boundedCounts_injective

instance : Fintype (TypeConfiguration I) := Fintype.ofFinite _

end TypeConfiguration

namespace FractionalCover

open Set
variable {I C : Type*} [Fintype I] [Fintype C]

def Feasible (a : C → I → ℝ) (d : I → ℝ) (w : C → ℝ) : Prop :=
  (∀ c, 0 ≤ w c) ∧ ∀ i, d i ≤ ∑ c, a c i * w c

def objective (w : C → ℝ) : ℝ := ∑ c, w c

def objectiveSet (a : C → I → ℝ) (d : I → ℝ) : Set ℝ :=
  {v | ∃ w, Feasible a d w ∧ objective w = v}

def value (a : C → I → ℝ) (d : I → ℝ) : ℝ :=
  sInf (objectiveSet a d)

end FractionalCover

def individualMatrix (I : Instance) (H : IndividualConfiguration I) (i : I.Item) : ℝ :=
  if i ∈ H.val then 1 else 0

def individualLP (I : Instance) : ℝ :=
  FractionalCover.value (individualMatrix I) (fun _ => 1)

def typeMatrix (I : Instance) (c : TypeConfiguration I) (s : NumericalSize I) : ℝ :=
  c.val s

def typeLP (I : Instance) : ℝ :=
  FractionalCover.value (typeMatrix I) (fun s => (s.multiplicity : ℝ))

abbrev RawInstance := List (ℕ × ℕ)

abbrev RawReductionOutput := ℕ × RawInstance

namespace RawInstance

def Valid (r : RawInstance) : Prop :=
  ∀ q ∈ r, 0 < q.1 ∧ q.1 ≤ q.2

def ratValue (q : ℕ × ℕ) : ℚ := (q.1 : ℚ) / (q.2 : ℚ)

theorem den_pos {r : RawInstance} (hr : r.Valid) {q : ℕ × ℕ} (hq : q ∈ r) :
    0 < q.2 := lt_of_lt_of_le (hr q hq).1 (hr q hq).2

def toInstance (r : RawInstance) (hr : r.Valid) : Instance where
  n := r.length
  size i := ratValue (r.get i)
  size_pos i := div_pos (Nat.cast_pos.mpr (hr _ (List.get_mem r i)).1)
    (Nat.cast_pos.mpr (den_pos hr (List.get_mem r i)))
  size_le_one i := (div_le_one₀ (Nat.cast_pos.mpr (den_pos hr (List.get_mem r i)))).mpr
    (Nat.cast_le.mpr (hr _ (List.get_mem r i)).2)

end RawInstance

structure RawPacking where
  bins : ℕ
  assignments : List ℕ

namespace RawPacking

def load (r : RawInstance) (a : List ℕ) (j : ℕ) : ℚ :=
  ((r.zip a).map fun qa =>
    if qa.2 = j then RawInstance.ratValue qa.1 else 0).sum

def Feasible (r : RawInstance) (p : RawPacking) : Prop :=
  p.assignments.length = r.length ∧
  (∀ j ∈ p.assignments, j < p.bins) ∧
  ∀ j < p.bins, load r p.assignments j ≤ 1

end RawPacking

namespace BinaryEncoding

abbrev natBits := BinPackingCompleteness.BinaryEncoding.nameBits

abbrev parseNat := BinPackingCompleteness.BinaryEncoding.parseName

def listBits {α : Type} (encode : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: rest => true :: (encode a ++ listBits encode rest)

def pairBits {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (p : α × β) : List Bool := ea p.1 ++ eb p.2

def optionBits {α : Type} (encode : α → List Bool) : Option α → List Bool
  | none => [false]
  | some a => true :: encode a

abbrev Parser (α : Type) := List Bool → Option (α × List Bool)

def parsePair {α β : Type} (pa : Parser α) (pb : Parser β) : Parser (α × β) :=
  fun input => do
    let (a, rest) ← pa input
    let (b, suffix) ← pb rest
    return ((a, b), suffix)

def parseListAux {α : Type} (parse : Parser α) : Nat → Parser (List α)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: rest => do
    let (a, rest) ← parse rest
    let (as, suffix) ← parseListAux parse fuel rest
    return (a :: as, suffix)

def parseList {α : Type} (parse : Parser α) : Parser (List α) :=
  fun input => parseListAux parse input.length input

def decode {α : Type} (parse : Parser α) (input : List Bool) : Option α := do
  let (a, rest) ← parse input
  if rest.isEmpty then some a else none

def rawInstanceBits (r : RawInstance) : List Bool :=
  listBits (pairBits natBits natBits) r

def assignmentBits (a : List Nat) : List Bool := listBits natBits a

def rawPackingBits (p : RawPacking) : List Bool :=
  natBits p.bins ++ assignmentBits p.assignments

def packingResultBits (p : Option RawPacking) : List Bool := optionBits rawPackingBits p

def rawReductionOutputBits (out : RawReductionOutput) : List Bool :=
  natBits out.1 ++ rawInstanceBits out.2

def parseRawInstance : Parser RawInstance := parseList (parsePair parseNat parseNat)

def decodeRawInstance := decode parseRawInstance

end BinaryEncoding

section

open Turing BinPackingGames.Foundations.Complexity

abbrev BitLanguage := List Bool → Prop

def InP (L : BitLanguage) : Prop :=
  ∃ decider : List Bool → Bool,
  ∃ computation : TM2ComputableInPolyTime
      (id : List Bool → List Bool) (fun b => [b]) decider,
    MachineFiniteAlphabet.FiniteAlphabet computation.tm ∧
    ∀ x, L x ↔ decider x = true

def ClassP : Set BitLanguage := {L | InP L}

def ClassNP : Set BitLanguage := {L | CookLevin.InNP L}

def PEqualsNP : Prop := ClassP = ClassNP

structure AbsoluteAdditiveAlgorithm (c : Nat) where
  run : List Bool → Option RawPacking
  computation : TM2ComputableInPolyTime (id : List Bool → List Bool)
    BinaryEncoding.packingResultBits run
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  guarantee : ∀ (r : RawInstance) (hr : r.Valid), ∃ p : RawPacking,
    run (BinaryEncoding.rawInstanceBits r) = some p ∧
    RawPacking.Feasible r p ∧ p.bins ≤ opt (r.toInstance hr) + c

structure PackingGapReduction (c : Nat) (L : BitLanguage) where
  reduce : List Bool → RawReductionOutput
  computation : TM2ComputableInPolyTime (id : List Bool → List Bool)
    BinaryEncoding.rawReductionOutputBits reduce
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  valid : ∀ x, (reduce x).2.Valid
  itemCount : ∀ x, (reduce x).2.length = 5 * (reduce x).1
  itemLower : ∀ x i,
    (1 / 6 : ℚ) < ((reduce x).2.toInstance (valid x)).size i
  completeness : ∀ x, L x →
    HasPacking ((reduce x).2.toInstance (valid x)) (reduce x).1
  soundness : ∀ x, ¬L x →
    ¬HasPacking ((reduce x).2.toInstance (valid x)) ((reduce x).1 + c)

def PackingGapNPHard (c : Nat) : Prop :=
  ∀ L : BitLanguage, CookLevin.InNP L → Nonempty (PackingGapReduction c L)

end

def main_results_statement : Prop :=
  (∀ c : ℕ, ∃ I : Instance, ∃ B : ℕ,
      I.n = 5 * B ∧
      (∀ i, (1 / 6 : ℚ) < I.size i ∧ I.size i < 1) ∧
      B + c < opt I ∧ individualLP I = (B : ℝ) ∧ typeLP I = (B : ℝ)) ∧
    (∀ c : Nat, PackingGapNPHard c) ∧
    ((∃ c : Nat, Nonempty (AbsoluteAdditiveAlgorithm c)) ↔ PEqualsNP) ∧
    (PEqualsNP → ∃ algorithm : AbsoluteAdditiveAlgorithm 0,
    (∀ (items : RawInstance) (valid : items.Valid), ∃ packing : RawPacking,
      algorithm.run (BinaryEncoding.rawInstanceBits items) = some packing ∧
      packing.Feasible items ∧ packing.bins = opt (items.toInstance valid)) ∧
    algorithm.run (BinaryEncoding.rawInstanceBits []) = some ⟨0, []⟩ ∧
    (∀ input : List Bool, BinaryEncoding.decodeRawInstance input = none →
      algorithm.run input = none) ∧
    (∀ items : RawInstance, ¬ items.Valid →
      algorithm.run (BinaryEncoding.rawInstanceBits items) = none))

end BinPackingGap

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.BinPackingGap.main_results_statement

end Problem

/- Formalization scope, from lean/docs/118.md: The formalized results rule out a universal additive bound for the configuration linear program in bin packing. For every integer $c\ge0$, there are an integer $B$ and a rational instance with $5B$ items whose individual-copy and size-type configuration-LP values both equal $B$, but whose integral optimum is greater than $B+c$. Distinguishing a packing in $B$ bins from the absence of one in $B+c$ bins is NP-hard for each fixed $c$. A deterministic polynomial-time algorithm with a fixed absolute additive allowance exists exactly when $P=NP$; under that equality, an optimal algorithm is constructed. -/
