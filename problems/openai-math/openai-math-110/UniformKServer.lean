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

- problem_id: UniformKServer
- collection: openai-math
- question_id: openai-math:110
- source: openai-math
- source_locator: lean/ComparatorChallenges/UniformKServer.lean#OAI.UniformKServer.uniform_squared_logarithmic_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Establishes a randomized competitive ratio $`O(\log^2(k+1))`$ for k-server on every metric space, matching the worst-case lower-bound order. One policy serves every finite oblivious request sequence, including on infinite unbounded metrics. On finite rational metrics, a uniform implementation has polynomial preprocessing and per-request bit cost in the input length and $`\log(t+1)`$ at request t, with a finite instance-dependent additive movement constant. ([Lean](lean/docs/110.md)) We prove that randomized k-server has competitive ratio $`O((\log(k+1))^2)`$ on every metric space against oblivious request sequences, matching the known worst-case lower bound. For each metric and initial configuration, one policy works for all finite request sequences, including on infinite and unbounded spaces. When the initial server positions are distinct, no additive term is needed. We construct a uniform randomized k-server algorithm on finite rational metrics with competitive ratio $`O(\log^2(k+1))`$ against oblivious request sequences. Preprocessing is polynomial in the input length, and per-request bit complexity is polynomial in that length and the binary request-counter length. The additive movement constant is finite and instance-dependent, but may be enormous. The construction uses the companion squared-logarithmic existence theorem.
- notes: OpenAI math result family 110, Optimal-order randomized <i>k</i>-server on arbitrary metrics -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/110.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.UniformKServer.uniform_squared_logarithmic_main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.UniformKServer.Main
- source_papers: preprints/Squared-logarithmic-randomized-k-server-on-arbitrary-metrics-September-24-2026/Squared-logarithmic-randomized-k-server-on-arbitrary-metrics-September-24-2026.pdf preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf
- source_scope_note: lean/docs/110.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

   

                                                                               

  
namespace UniformKServer

structure RationalMetric (n : ℕ) where
  distance : Fin n → Fin n → ℚ
  nonneg : ∀ x y, 0 ≤ distance x y
  eq_zero : ∀ x y, distance x y = 0 ↔ x = y
  symm : ∀ x y, distance x y = distance y x
  triangle : ∀ x y z, distance x z ≤ distance x y + distance y z

abbrev Configuration (n k : ℕ) := Fin k → Fin n
abbrev History (n k : ℕ) := List (Fin n × Fin k)

def serve {n k : ℕ} (s : Configuration n k) (r : Fin n) (j : Fin k) :
    Configuration n k := Function.update s j r

def costAlong {n k : ℕ} (d : RationalMetric n) :
    Configuration n k → History n k → ℝ
  | _, [] => 0
  | s, (r, j) :: h => (d.distance (s j) r : ℝ) + costAlong d (serve s r j) h

/-- All finite serving-label choices, knowing the entire request word. -/
noncomputable def offlineCost {n k : ℕ} (d : RationalMetric n) (s : Configuration n k)
    (w : List (Fin n)) : ℝ :=
  sInf {c | ∃ h : History n k, h.map Prod.fst = w ∧ c = costAlong d s h}

inductive HeadMove where
  | left | stay | right
  deriving DecidableEq

structure BitTape where
  left : List (Option Bool)
  head : Option Bool
  right : List (Option Bool)

namespace BitTape

def blank : BitTape := ⟨[], none, []⟩

def ofWord (w : List Bool) : BitTape :=
  match w with
  | [] => blank
  | b :: bs => ⟨[], some b, bs.map some⟩

def shift (T : BitTape) : HeadMove → BitTape
  | .stay => T
  | .left => match T.left with
    | [] => ⟨[], none, T.head :: T.right⟩
    | a :: as => ⟨as, a, T.head :: T.right⟩
  | .right => match T.right with
    | [] => ⟨T.head :: T.left, none, []⟩
    | a :: as => ⟨T.head :: T.left, a, as⟩

end BitTape

structure BitAction (q m : ℕ) where
  control : Fin q
  inputMove : HeadMove
  write : Fin m → Option Bool
  workMove : Fin m → HeadMove
  emit : Option Bool
  yield : Bool

structure BitMachine where
  controls : ℕ
  tapes : ℕ
  start : Fin controls
  transition : Fin controls → Option Bool → (Fin tapes → Option Bool) →
    Bool → BitAction controls tapes

structure MachineState (M : BitMachine) where
  control : Fin M.controls
  input : BitTape
  work : Fin M.tapes → BitTape
  outputRev : List Bool
  yielded : Bool

namespace BitMachine

def initial (M : BitMachine) (input : List Bool) : MachineState M :=
  ⟨M.start, BitTape.ofWord input, fun _ => BitTape.blank, [], false⟩

def step (M : BitMachine) (s : MachineState M) (coin : Bool) : MachineState M :=
  if s.yielded then s else
  let a := M.transition s.control s.input.head (fun i => (s.work i).head) coin
  { control := a.control
    input := s.input.shift a.inputMove
    work := fun i => ({s.work i with head := a.write i}).shift (a.workMove i)
    outputRev := match a.emit with
      | none => s.outputRev
      | some b => b :: s.outputRev
    yielded := a.yield }

def run (M : BitMachine) (s : MachineState M) (coins : List Bool) : MachineState M :=
  coins.foldl M.step s

/-- At a request boundary only the input/output interface is refreshed.
    Work tapes and control retain the complete internal state. -/
def install (M : BitMachine) (s : MachineState M) (input : List Bool) : MachineState M :=
  {s with input := BitTape.ofWord input, outputRev := [], yielded := false}

end BitMachine

/-- Self-delimiting binary code: ℓ ones, a zero, then ℓ low-to-high bits.
    This fixes one standard binary encoding rather than allowing a nonuniform
    advice string to be included in the input. -/
def natCode (a : ℕ) : List Bool :=
  List.replicate a.bits.length true ++ [false] ++ a.bits

def rationalCode (a : ℚ) : List Bool :=
  (a.num < 0) :: (natCode a.num.natAbs ++ natCode a.den)

def instanceCode {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) : List Bool :=
  natCode n ++ natCode k ++
    (List.ofFn fun x : Fin n =>
      (List.ofFn fun y : Fin n => rationalCode (d.distance x y)).flatten).flatten ++
    (List.ofFn fun j : Fin k => natCode ((s j).val + 1)).flatten

def bitValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitValue bs

def outputValue {M : BitMachine} (s : MachineState M) : ℕ :=
  bitValue s.outputRev.reverse

/-- A dominating polynomial; every fixed polynomial nonnegative on natural
    inputs is bounded by one of this form after increasing c and e. -/
def polynomialBudget (c e x : ℕ) : ℕ := c * (x + 1)^e

def requestBudget (c e L t : ℕ) : ℕ :=
  polynomialBudget c e (L + Nat.clog 2 (t + 1))

def boot {n k : ℕ} (M : BitMachine) (c e : ℕ)
    (d : RationalMetric n) (s : Configuration n k) : MachineState M :=
  M.run (M.initial (instanceCode d s))
    (List.replicate (polynomialBudget c e (instanceCode d s).length) false)

def requestStep {n : ℕ} (M : BitMachine) (c e L t : ℕ)
    (s : MachineState M) (r : Fin n)
    (coins : Fin (requestBudget c e L t) → Bool) : MachineState M :=
  M.run (M.install s (natCode (r.val + 1))) (List.ofFn coins)

/-- Reachability includes every binary choice, not merely an almost-sure set.
    The index counts requests already served. -/
inductive Reachable {n k : ℕ} (M : BitMachine) (c e : ℕ)
    (d : RationalMetric n) (s : Configuration n k) : ℕ → MachineState M → Prop
  | boot : Reachable M c e d s 0 (boot M c e d s)
  | next {t z} : Reachable M c e d s t z → (r : Fin n) →
      (bits : Fin (requestBudget c e (instanceCode d s).length (t+1)) → Bool) →
      Reachable M c e d s (t+1)
        (requestStep M c e (instanceCode d s).length (t+1) z r bits)

/-- Modulo makes the semantic recursion total even for unsuccessful machines.
    The main statement separately requires the output to be < k at *every*
    reachable outcome, so no invalid output is accepted or silently repaired. -/
def selectedLabel {M : BitMachine} {k : ℕ} (hk : 0 < k) (s : MachineState M) : Fin k :=
  ⟨outputValue s % k, Nat.mod_lt _ hk⟩

noncomputable def machineExpectedCost {n k : ℕ} (M : BitMachine) (c e L : ℕ)
    (d : RationalMetric n) (hk : 0 < k) :
    ℕ → MachineState M → Configuration n k → List (Fin n) → ℝ
  | _, _, _, [] => 0
  | t, z, s, r :: w =>
      let B := requestBudget c e L (t+1)
      (∑ bits : Fin B → Bool,
        let z' := requestStep M c e L (t+1) z r bits
        let j := selectedLabel hk z'
        (d.distance (s j) r : ℝ) +
          machineExpectedCost M c e L d hk (t+1) z' (serve s r j) w) / (2 : ℝ)^B

/-- Full uniform main objective in the explicit bit model, not a theorem or
    assumption. Machine transition steps are bit operations. Installing the
    standard input and reading/erasing the output adds only O(L + budget)
    charged bit operations, hence is absorbed by a single larger polynomial.
    A single deterministic boot is sufficient for the source construction. -/
def UniformAlgorithmClaim : Prop :=
  ∃ (M : BitMachine) (c e : ℕ) (C : ℝ), 0 < c ∧ 0 < C ∧
    ∀ (n k : ℕ) (hn : 3 ≤ n) (hk : 2 ≤ k) (hkn : k < n)
      (d : RationalMetric n) (s : Configuration n k),
      let L := (instanceCode d s).length
      (boot M c e d s).yielded = true ∧
      (∀ (t : ℕ) (z : MachineState M), Reachable M c e d s t z →
        ∀ (r : Fin n) (bits : Fin (requestBudget c e L (t+1)) → Bool),
          let z' := requestStep M c e L (t+1) z r bits
          z'.yielded = true ∧ outputValue z' < k) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ w : List (Fin n),
        machineExpectedCost M c e L d (by omega) 0 (boot M c e d s) s w ≤
          C * (Real.log (k + 1))^2 * offlineCost d s w + B)

/-- A single uniform randomized bit machine has squared-logarithmic expected movement
and a uniform polynomial bound on each request's bit operations. -/
def uniform_squared_logarithmic_main_statement : Prop :=
  UniformAlgorithmClaim

end UniformKServer

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.UniformKServer.uniform_squared_logarithmic_main_statement

end Problem

/- Formalization scope, from lean/docs/110.md: The formalization proves an $O((\log(k+1))^2)$ competitive ratio for randomized $k$-server against oblivious finite request sequences. For every $k\ge2$, every metric space containing at least $k+1$ points, and every initial configuration, one policy works for all request sequences, including in infinite and unbounded spaces. The bound permits a configuration-dependent additive constant, which is zero when the initial server positions are distinct. The universal multiplicative constant is independent of the metric and $k$. The formalization constructs one uniform randomized bit algorithm for $k$-server on finite rational metrics, for $2\le k<n$. Its expected movement on every oblivious finite request sequence is at most an absolute multiple of $(\log(k+1))^2$ times the offline optimum, plus a finite instance-dependent additive constant. Preprocessing is polynomial in the encoded input length, and each request is processed in time polynomial in that length and the binary length of the request counter. Every processed request returns a legal server index. The additive movement constant is not claimed to be polynomially bounded. -/
