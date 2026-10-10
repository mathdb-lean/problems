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

- problem_id: CoordinateSweeps
- collection: openai-math
- question_id: openai-math:238
- source: openai-math
- source_locator: lean/ComparatorChallenges/CoordinateSweeps.lean#OAI.CoordinateSweeps.conditional_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the Thorp shuffle randomizes $`N=2^d`$ labeled cards in $`\Theta(\log N)`$ physical shuffles, settling its optimal mixing order for power-of-two deck sizes. Convergence is in total variation from the worst initial ordering and concerns the entire permutation, not just individual card positions. ([Lean](lean/docs/238.md)) We prove that the Thorp shuffle on $`2^d`$ cards mixes in $`\Theta(d)`$ complete shuffles. The full permutation law after $`1600d`$ shuffles converges to uniform in total variation as $`d\to\infty`$, uniformly over the initial deck, while a support count gives a lower bound of $`2d-O(1)`$. We show how information about partial permutations controls full permutation laws. Let n tend to infinity through multiples of eight. If the images of a uniformly chosen $`7n/8`$ labels approach the uniform injection law in average total variation, and the sign mean tends to zero, then the product of two independent permutations with the given law converges to uniform on Sn. Fix half the labels in a Thorp shuffle on $`2^d`$ positions and reveal their complete trajectories. We prove that, after an explicit absolute number of coordinate sweeps, the conditional permutation of the remaining labels approaches uniform in expected total variation as $`d\to\infty`$, uniformly in the initial layout. The resulting constructions give full-deck mixing in a constant multiple of d physical shuffles. For $`N=2^d`$ cards, we prove that an absolute number of coordinate sweeps of the Thorp shuffle brings the full permutation law to total-variation distance tending to zero from uniform. The mixing time therefore has optimal order $`\Theta(\log N)`$ in physical shuffles. We prove that the Thorp shuffle on $`N=2^d`$ labeled cards has full-permutation total-variation mixing time $`\Theta(\log N)`$ in physical shuffles. An absolute number of coordinate sweeps suffices for the upper bound. We prove that an absolute number of coordinate sweeps of the Thorp shuffle on $`n=2^d`$ positions brings the full permutation to total-variation distance at most $`\frac12n^{-5}`$ from uniform, uniformly over the initial deck. Thus $`O(d)`$ physical shuffles suffice, which is optimal in order. We prove that the Thorp shuffle on $`n=2^d`$ cards mixes in $`\Theta(d)`$ physical shuffles. After a sufficiently large fixed number of coordinate sweeps, the total-variation distance of the full permutation from uniform tends to zero as $`d\to\infty`$. We prove that a fixed number of coordinate sweeps of the Thorp shuffle on $`2^d`$ cards makes the squared L2 distance of the full permutation density from uniform tend to zero as $`d\to\infty`$. In particular, the total-variation mixing time is $`\Theta(d)`$ physical shuffles. For coordinate sweeps with near-uniform line laws and line sizes among powers of two in a suitable fixed interval, we prove a Schatten-moment bound after conditioning on any feasible collection of prescribed card trajectories. An analytic transfer to binary sweeps then shows that a fixed number of sweeps mixes the Thorp shuffle on $`2^d`$ cards in $`O(d)`$ physical steps, matching the order of the support lower bound. We prove a permanent inequality with exponent strictly below two for laws on S4 sufficiently close to uniform and with exactly uniform coordinate marginals. Applied to a four-row recursion, it shows that an absolute number of coordinate sweeps brings the full permutation of the Thorp shuffle on $`N=2^d`$ cards to total-variation distance tending to zero from uniform as $`N\to\infty`$. Thus the mixing time has the optimal order $`O(\log N)`$ in physical shuffles.
- notes: OpenAI math result family 238, Optimal logarithmic mixing of the Thorp shuffle -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/238.md
- track: solved
- answer_shape: proof
- context_lemmas: reference_compatible
- source_theorem: OAI.CoordinateSweeps.conditional_main OAI.CoordinateSweeps.all_grid_moment
- source_theorem_count: 2
- source_solution_module: OAI.Probability.CoordinateSweeps.Main
- source_main_result: OAI.CoordinateSweeps.conditional_main
- source_papers: preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf preprints/From-partial-permutation-information-to-Fourier-bounds-September-26-2026/main.pdf preprints/Conditional-permutations-in-a-revealed-switching-environment-September-26-2026/paper.pdf preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf preprints/Random-subspace-tests-and-trace-smoothing-for-coordinate-sweeps-September-26-2026/paper.pdf preprints/Compatibility-entropy-and-the-spectrum-of-a-Thorp-sweep-September-26-2026/paper.pdf preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf preprints/Conditional-coordinate-sweeps-and-analytic-transfer-September-26-2026/main.pdf preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/main.pdf
- source_scope_note: lean/docs/238.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
Conditional moments for one ordered coordinate sweep on power-of-two rectangular
grids. The line law mixes uniform permutations with a binary coordinate sweep.
The trace is unnormalized, and the trajectory cost uses falling factorials.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ComplexConjugate MatrixOrder ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

structure FiniteLaw (Ω : Type*) where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ᶠ x, mass x = 1

namespace FiniteLaw

variable {Ω X Y : Type*}

instance : CoeFun (FiniteLaw Ω) (fun _ => Ω → ℝ) := ⟨FiniteLaw.mass⟩

@[ext] theorem ext {μ ν : FiniteLaw Ω} (h : ∀ x, μ x = ν x) : μ = ν := by
  cases μ
  cases ν
  congr
  exact funext h

variable [Fintype Ω] [Fintype X] [Fintype Y]

@[simp] theorem sum_mass (μ : FiniteLaw Ω) : ∑ x, μ x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using μ.total

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    rw [finsum_eq_sum_of_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

def map (μ : FiniteLaw Ω) (f : Ω → X) : FiniteLaw X where
  mass y := ∑ x, if f x = y then μ x else 0
  nonneg y := Finset.sum_nonneg (fun x _ => by split_ifs; exact μ.nonneg x; exact le_rfl)
  total := by
    rw [finsum_eq_sum_of_fintype]
    classical
    rw [Finset.sum_comm]
    simp [μ.sum_mass]

end FiniteLaw

abbrev Cube (d : ℕ) := Fin d → Bool

def pairSwitch {L : Type*} (bits : L → Bool) : Equiv.Perm (Bool × L) where
  toFun x := (Bool.xor x.1 (bits x.2), x.2)
  invFun x := (Bool.xor x.1 (bits x.2), x.2)
  left_inv point := by
    rcases point with ⟨bit, label⟩
    change ((bit ^^ bits label) ^^ bits label, label) = (bit, label)
    cases bit <;> cases bits label <;> simp
  right_inv point := by
    rcases point with ⟨bit, label⟩
    change ((bit ^^ bits label) ^^ bits label, label) = (bit, label)
    cases bit <;> cases bits label <;> simp

def binaryLayer {d : ℕ} (j : Fin d) (bits : ({k : Fin d // k ≠ j} → Bool) → Bool) :
    Equiv.Perm (Cube d) :=
  (Equiv.funSplitAt j Bool).trans ((pairSwitch bits).trans (Equiv.funSplitAt j Bool).symm)

/-- Coordinate zero acts first. -/
def orderedProduct {G : Type*} [Monoid G] {d : ℕ} (g : Fin d → G) : G :=
  (List.ofFn g).reverse.prod

abbrev BinaryChoices (d : ℕ) := ∀ j : Fin d, ({k : Fin d // k ≠ j} → Bool) → Bool

instance (d : ℕ) : Nonempty (BinaryChoices d) := ⟨fun _ _ => false⟩

def binarySweep (d : ℕ) (bits : BinaryChoices d) : Equiv.Perm (Cube d) :=
  orderedProduct (fun j => binaryLayer j (bits j))

def binaryLaw (d : ℕ) : FiniteLaw (Equiv.Perm (Cube d)) :=
  (FiniteLaw.uniform (BinaryChoices d)).map (binarySweep d)

structure Grid where
  b : ℕ
  positive : 0 < b
  bits : Fin b → ℕ

namespace Grid

def size (G : Grid) : ℕ := ∏ j, 2 ^ G.bits j

abbrev Slot (G : Grid) := ∀ j, Cube (G.bits j)

abbrev Line (G : Grid) (j : Fin G.b) := ∀ k : {k : Fin G.b // k ≠ j}, Cube (G.bits k)

abbrev Choices (G : Grid) := ∀ j, G.Line j → Equiv.Perm (Cube (G.bits j))

def fiberPerm {A B : Type*} (p : B → Equiv.Perm A) : Equiv.Perm (A × B) where
  toFun x := (p x.2 x.1, x.2)
  invFun x := ((p x.2).symm x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

def stage (G : Grid) (ω : G.Choices) (j : Fin G.b) : Equiv.Perm G.Slot :=
  (Equiv.piSplitAt j (fun k => Cube (G.bits k))).trans
    ((fiberPerm (ω j)).trans (Equiv.piSplitAt j (fun k => Cube (G.bits k))).symm)

def boundary (G : Grid) (ω : G.Choices) (t : ℕ) : Equiv.Perm G.Slot :=
  ((List.ofFn (G.stage ω)).take t).reverse.prod

def sweep (G : Grid) (ω : G.Choices) : Equiv.Perm G.Slot := G.boundary ω G.b

/-- The side lengths are in `[R, R²]`, where the single global scale is `R = 2^r`. -/
def Allowed (G : Grid) (r : ℕ) : Prop := ∀ j, r ≤ G.bits j ∧ G.bits j ≤ 2 * r

/-- Full disjoint paths, including every boundary of the ordered sweep. -/
structure Holes (G : Grid) (h : ℕ) where
  path : Fin h → Fin (G.b + 1) → G.Slot
  disjoint : ∀ t, Function.Injective (fun i => path i t)
  coordinate_step : ∀ i (j : Fin G.b) (k : Fin G.b), k ≠ j →
    path i j.succ k = path i j.castSucc k

namespace Holes

variable {G : Grid} {h : ℕ}

def Compatible (H : G.Holes h) (ω : G.Choices) : Prop :=
  ∀ i (t : Fin (G.b + 1)), G.boundary ω t (H.path i 0) = H.path i t

def Feasible (H : G.Holes h) : Prop := ∃ ω, H.Compatible ω

def lineCount (H : G.Holes h) (j : Fin G.b) (L : G.Line j) : ℕ :=
  (Finset.univ.filter (fun i : Fin h =>
    (fun k : {k : Fin G.b // k ≠ j} => H.path i j.castSucc k) = L)).card

def cost (H : G.Holes h) : ℝ :=
  ∑ j, ∑ L : G.Line j,
    Real.log (((2 ^ G.bits j : ℕ) : ℝ) ^ H.lineCount j L /
      ((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ))

/-- The symmetric group on the unmarked input sites. -/
def stabilizer (H : G.Holes h) : Subgroup (Equiv.Perm G.Slot) where
  carrier g := ∀ i, g (H.path i 0) = H.path i 0
  one_mem' _ := rfl
  mul_mem' := by
    intro g g' hg hg' i
    change g (g' (H.path i 0)) = H.path i 0
    rw [hg' i, hg i]
  inv_mem' hg i := (Equiv.symm_apply_eq _).mpr (hg i).symm

def reference (H : G.Holes h) (hf : H.Feasible) : G.Choices := hf.choose

theorem reference_compatible (H : G.Holes h) (hf : H.Feasible) :
    H.Compatible (H.reference hf) := hf.choose_spec

/-- A reference completion identifies the free input and output sites. -/
def residual (H : G.Holes h) (hf : H.Feasible) (ω : {ω : G.Choices // H.Compatible ω}) :
    H.stabilizer :=
  ⟨(G.sweep (H.reference hf))⁻¹ * G.sweep ω.val, by
    intro i
    change (G.sweep (H.reference hf)).symm (G.sweep ω.val (H.path i 0)) = H.path i 0
    apply (Equiv.symm_apply_eq _).mpr
    exact (ω.property i (Fin.last _)).trans ((H.reference_compatible hf i (Fin.last _)).symm)⟩

end Holes

/-- Independent line permutations with law `(1-z) U + z B`. -/
def choiceWeight (G : Grid) (z : ℝ) (ω : G.Choices) : ℝ :=
  ∏ j, ∏ L : G.Line j,
    ((1-z) * (Fintype.card (Equiv.Perm (Cube (G.bits j))) : ℝ)⁻¹ +
      z * binaryLaw (G.bits j) (ω j L))

namespace Holes

variable {G : Grid} {h : ℕ}

def probability (H : G.Holes h) (z : ℝ) : ℝ :=
  ∑ ω : {ω : G.Choices // H.Compatible ω}, G.choiceWeight z ω.val

end Holes

def eventDistance (G : Grid) (E : Finset G.Choices) (z : ℝ) : ℝ :=
  ∑ ω ∈ E, |G.choiceWeight z ω/(∑ v ∈ E, G.choiceWeight z v)-
    G.choiceWeight 0 ω/(∑ v ∈ E, G.choiceWeight 0 v)|

end Grid

structure UnitaryIrrep (Γ : Type*) [Group Γ] where
  dimension : ℕ
  positive : 0 < dimension
  matrix : Γ →* Matrix (Fin dimension) (Fin dimension) ℂ
  unitary : ∀ g, (matrix g).conjTranspose * matrix g = 1
  irreducible : ∀ S : Submodule ℂ (Fin dimension → ℂ),
    (∀ g v, v ∈ S → (matrix g).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤

/-- Unnormalized Schatten `2q` moment, without division by the dimension. -/
def schattenMoment {D : ℕ} (q : ℕ) (K : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (Matrix.trace ((K.conjTranspose * K) ^ q)).re

namespace Grid.Holes

variable {G : Grid} {h : ℕ}

def conditionalAverage (H : G.Holes h) (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ :=
  (H.probability z : ℂ)⁻¹ •
    ∑ ω : {ω : G.Choices // H.Compatible ω},
      (G.choiceWeight z ω.val : ℂ) • ρ.matrix (H.residual hf ω)

end Grid.Holes

def a : ℝ := 1 / 100
def c0 : ℝ := a / 100
def e0 : ℝ := a / 100
def c (s : ℕ) : ℝ := c0 + 1 / Real.sqrt (Real.log s)
def e (s : ℕ) : ℝ := e0 - 1 / Real.sqrt (Real.log s)

/-- The logarithm of a zero moment is minus infinity. -/
def logMoment (t : ℝ) : EReal := if t = 0 then ⊥ else (Real.log t : EReal)

def ConditionalMain : Prop :=
  ∃ (r q : ℕ) (zStar : ℝ), 1 ≤ r ∧ 1 ≤ q ∧ 0 < zStar ∧ zStar ≤ 1 / ((2 : ℕ) : ℝ) ∧
    ∀ (G : Grid), G.Allowed r → ∀ (h : ℕ) (H : G.Holes h) (hf : H.Feasible),
    ∀ z ∈ Set.Icc 0 zStar, ∀ ρ : UnitaryIrrep H.stabilizer,
      logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
        ((-c G.size * Real.log ρ.dimension + e G.size * h * Real.log G.size - H.cost : ℝ) : EReal)

def MomentBound (G : Grid) (q : ℕ) (z : ℝ) : Prop :=
  ∀ (h : ℕ) (H : G.Holes h) (hf : H.Feasible) (σ : UnitaryIrrep H.stabilizer),
    schattenMoment q (H.conditionalAverage hf z σ) ≤
      Real.exp (-c G.size*Real.log σ.dimension+e G.size*h*Real.log G.size-H.cost)

def ScaleLarge (r : ℕ) : Prop :=
  1 ≤ r ∧ (2/e0)^2 ≤ (r : ℝ)*Real.log 2 ∧ 4/e0 ≤ (r : ℝ)*Real.log 2

def baseWidth (r : ℕ) : ℝ := ((2^(2*r)).factorial : ℕ)
def baseZeta (r : ℕ) : ℝ := 1/(4*(baseWidth r)^2)

namespace ScalarInduction

structure MainSizeReady (q : ℕ) (s : ℝ) : Prop where
  one : 1 ≤ Real.log s
  sparse : (100004:ℝ)*s^(1-a/4) ≤ s^(1-(1:ℝ)/1600)
  hook : (((2*q+1:ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a)*Real.log (s+1) ≤ s^((9:ℝ)/10)
  removed : s^((9:ℝ)/10)+s^(1-a/2)*Real.log s ≤ s^(1-a/4)/(20*Real.sqrt (Real.log s))

end ScalarInduction

namespace SparseScalar

def theta : ℝ := 1/1600
def K0 : ℝ := 100000
def B0 : ℕ := 12800
def xi : ℝ := 1/2048000000
def rho : ℝ := 1/32768000000
def q : ℕ := 65536000000

def uniformRate : ℝ := Real.log ((2 : ℕ) : ℝ) + (B0 : ℝ) *
  (K0 + 1 + Real.log ((4 : ℕ) : ℝ) +
    Real.log (((16 : ℕ) : ℝ) * Real.exp ((2 : ℕ) : ℝ)) +
    Real.log (1 + ((16 : ℕ) : ℝ) * Real.exp ((2 : ℕ) : ℝ)))

structure SizeReady (s : ℝ) : Prop where
  two : 2 ≤ s
  logpow : Real.log s ≤ s^(theta/4)
  powtwo : 2 ≤ s^(theta/4)
  powB : (B0+1:ℝ) ≤ s^(theta/2)
  count : 4/s^(1/(4*(B0:ℝ))) ≤ theta/(64*B0)
  absorb : Real.log (1+2*(B0:ℝ))+Real.log 2 ≤ xi*Real.log s
  eta : s^(-xi) ≤ 1/8
  prefactor : uniformRate ≤ xi*Real.log s/16
  logtwo : Real.log 2 ≤ xi*Real.log s/8

structure ScaleReady (r : ℕ) : Prop where
  two : 2 ≤ r
  logone : 1 ≤ (r:ℝ)*Real.log 2
  absorb : 3*Real.log 2+2*(K0+1+Real.log 4) ≤ theta*((r:ℝ)*Real.log 2)/8
  size : ∀ s : ℝ, (2:ℝ)^r ≤ s → SizeReady s

def slack (s : ℝ) : ℝ :=
  if 1 < s then s ^ (-((2 : ℕ) : ℝ) * rho * s) * (s ^ rho - 1) else 1

end SparseScalar

def SparsePerturb (r : ℕ) (zStar : ℝ) : Prop :=
  0 < zStar ∧ zStar ≤ baseZeta r ∧ ∀ G : Grid, G.b ≤ SparseScalar.B0 → G.Allowed r →
    ∀ z ∈ Set.Icc 0 zStar, ∀ E : Finset G.Choices, E.Nonempty →
      G.eventDistance E z < SparseScalar.slack G.size

/-- The quantitative all-grid estimate under the explicit scale and perturbation bounds. -/
def all_grid_moment_statement : Prop :=
  ∀ {r : ℕ} (hr : ScaleLarge r) (hrS : SparseScalar.ScaleReady r) (hS : ∀ G : Grid, G.Allowed r → ScalarInduction.MainSizeReady SparseScalar.q G.size) {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z∈Set.Icc 0 zStar),
    ∀ G : Grid, G.Allowed r → MomentBound G SparseScalar.q z

/-- One global choice of scale, moment order, and positive perturbation interval. -/
def conditional_main_statement : Prop :=
  ConditionalMain

end CoordinateSweeps

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CoordinateSweeps.all_grid_moment_statement ∧
  _root_.OAI.CoordinateSweeps.conditional_main_statement

end Problem

/- Formalization scope, from lean/docs/238.md: The formalization proves optimal-order mixing of the Thorp shuffle on $2^d$ cards. After $1600d$ complete shuffles, the full permutation law converges in total variation to uniform as $d\to\infty$, uniformly over initial decks. Together with the support lower bound of $2d-O(1)$, this gives mixing time $\Theta(d)=\Theta(\log(2^d))$. The linked supporting results include frame and conditional-list estimates, regular trace and spectral bounds, signed moments, and full-density $L^2$ control. They also bound reciprocal Specht-dimension sums and give the eight-block Fourier estimate used in the mixing argument. The formalized supporting result turns bounds on partial-permutation cosets into Fourier bounds. Partition a finite set into $b\ge1$ nonempty blocks, and let $f\ge0$ be a subprobability weight on its symmetric group whose left-coset masses for each block subgroup are at most $B$. For every irreducible unitary representation of dimension $D$ and every $u>0$, both the squared Hilbert–Schmidt norm and squared operator norm of its Fourier transform are at most $bB\,C(u)D^{-1+(u+2)/b}$, where $C(u)$ is the stated symmetric-group degree constant. The paper's asymptotic conclusion about the product of two random permutations is outside this selected finite estimate. The formalized results give averaged conditional mixing for half-permutations in the revealed-path model and full-deck mixing for the Thorp shuffle. In particular, the full-deck total-variation distance tends to zero after $16040400d$ steps on $2^d$ cards, uniformly over deterministic initial decks. The conditional estimate is averaged over the actual outside-path law, rather than asserted for each individual environment. The formalization also includes the associated overlay, reset minorization, and two-color conditional constructions. The formalization covers nine routing and representation estimates for Thorp sweeps: adaptive operator and fourth-trace bounds, Casimir moments, dense truncation, sparse contact, harmonic-cycle contraction, smoothing, and three tail or sparse-saving estimates. They bound routing-density deviations and Fourier operators in dense and sparse regimes, including exponential savings in the level scale and representation dimension. The conditional high-height estimate requires a sufficiently large cutoff height $J$ that exceeds twice the number $s$ of coordinates in the fixed low block, so $J>2s$. These are the earlier nine statements associated with the paper; its changed later statements and six other result blocks are outside this scope. The formalization proves uniform representation bounds for one coordinate sweep of the Thorp shuffle. For each irreducible representation of dimension $D$, it chooses a weight between $D^{3/4}$ and $D$ and a Schatten exponent bounded by one absolute constant so that the weighted Schatten moment is at most one. The sweep's operator norm is consequently at most $D^{-c}$ for one absolute $c>0$. The supporting row–column estimate bounds the total squared overlap over all multiplicity copies on an occupied board, with explicit dependence on the row and column representation dimensions, the global dimension, the number of missing cells, and the number of rows or columns containing the global Young diagram. The paper's full physical-mixing conclusion is outside these selected representation estimates. The formalization proves a uniform trace-smoothing estimate for coordinate sweeps of the Thorp shuffle on $2^d$ cards. One absolute sweep parameter works for every $d\ge1$: the regular trace is at most $1+(2^d)^{-10}$, and the full permutation law after the corresponding fixed number of sweeps is within $\tfrac12(2^d)^{-5}$ of uniform in total variation, for every initial deck. Thus the selected upper bound uses $O(d)$ physical shuffles. The formalized result is the weighted compatibility theorem for balanced $A\times D$ rectangles, with $n=AD$ and $\sqrt n/2\le A,D\le2\sqrt n$. For arbitrary nonnegative weights on the row and column permutation groups, the normalized compatibility average is bounded by $\exp(C_0n^{54/100})$ times the product of the marginal $L^{1/\theta}$ factors, where $\theta=1-L/\log\sqrt n>0$ and the constants are absolute. Compatibility means injectivity in every original column. The bounded regular-moment and other moment/rank conclusions are not included. The formalization gives signed representation estimates for coordinate sweeps of the Thorp shuffle. For every signed occurrence of a Young diagram of size $2^d$, it bounds the logarithm of a fixed-order weighted sweep moment by a small multiple of the signed partition entropy plus an explicit remainder-size budget. The moment order is uniform over the diagrams and decompositions after the two small coefficients are fixed. The linked supporting angle bound controls the overlap of row, column, and global signed-type projections on an occupied rectangle, with explicit entropy, dimension, and missing-cell factors. These selected estimates support the paper's full-density argument; the full $L^2$ and total-variation mixing conclusion is outside them. The formalized binary-sweep theorem gives a universal power contraction in every irreducible representation: for sufficiently large $d$, the averaged sweep on $2^d$ slots has operator norm at most $D^{-g}$ in representation dimension $D$, for some $g>0$. The sign expectation is zero, and a fixed number of independent sweeps approaches uniform in total variation from every initial deck. A separate conditional moment estimate covers allowed power-of-two grids and disjoint coordinate-respecting trajectories, with its stated feasibility premise. Physical-shuffle law identification is not included. The formalization proves the paper's strict four-row permanent inequality. There are constants $4/3<p<2$ and $\varepsilon>0$ such that every probability law on $S_4$ within total-variation distance $\varepsilon$ of uniform, and with exactly uniform coordinate marginals, satisfies the permanent bound by the product of the four $L^p$ row norms for every nonnegative matrix. The exponent and neighborhood are uniform over those laws. The Thorp mixing consequence is outside this selected statement. -/
