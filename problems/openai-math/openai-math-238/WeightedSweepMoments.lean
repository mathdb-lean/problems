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

- problem_id: WeightedSweepMoments
- collection: openai-math
- question_id: openai-math:238
- source: openai-math
- source_locator: lean/ComparatorChallenges/WeightedSweepMoments.lean#OAI.CubeShuffle.WeightedSweep.weighted_sweep_moments
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the Thorp shuffle randomizes $`N=2^d`$ labeled cards in $`\Theta(\log N)`$ physical shuffles, settling its optimal mixing order for power-of-two deck sizes. Convergence is in total variation from the worst initial ordering and concerns the entire permutation, not just individual card positions. ([Lean](lean/docs/238.md)) We prove that the Thorp shuffle on $`2^d`$ cards mixes in $`\Theta(d)`$ complete shuffles. The full permutation law after $`1600d`$ shuffles converges to uniform in total variation as $`d\to\infty`$, uniformly over the initial deck, while a support count gives a lower bound of $`2d-O(1)`$. We show how information about partial permutations controls full permutation laws. Let n tend to infinity through multiples of eight. If the images of a uniformly chosen $`7n/8`$ labels approach the uniform injection law in average total variation, and the sign mean tends to zero, then the product of two independent permutations with the given law converges to uniform on Sn. Fix half the labels in a Thorp shuffle on $`2^d`$ positions and reveal their complete trajectories. We prove that, after an explicit absolute number of coordinate sweeps, the conditional permutation of the remaining labels approaches uniform in expected total variation as $`d\to\infty`$, uniformly in the initial layout. The resulting constructions give full-deck mixing in a constant multiple of d physical shuffles. For $`N=2^d`$ cards, we prove that an absolute number of coordinate sweeps of the Thorp shuffle brings the full permutation law to total-variation distance tending to zero from uniform. The mixing time therefore has optimal order $`\Theta(\log N)`$ in physical shuffles. We prove that the Thorp shuffle on $`N=2^d`$ labeled cards has full-permutation total-variation mixing time $`\Theta(\log N)`$ in physical shuffles. An absolute number of coordinate sweeps suffices for the upper bound. We prove that an absolute number of coordinate sweeps of the Thorp shuffle on $`n=2^d`$ positions brings the full permutation to total-variation distance at most $`\frac12n^{-5}`$ from uniform, uniformly over the initial deck. Thus $`O(d)`$ physical shuffles suffice, which is optimal in order. We prove that the Thorp shuffle on $`n=2^d`$ cards mixes in $`\Theta(d)`$ physical shuffles. After a sufficiently large fixed number of coordinate sweeps, the total-variation distance of the full permutation from uniform tends to zero as $`d\to\infty`$. We prove that a fixed number of coordinate sweeps of the Thorp shuffle on $`2^d`$ cards makes the squared L2 distance of the full permutation density from uniform tend to zero as $`d\to\infty`$. In particular, the total-variation mixing time is $`\Theta(d)`$ physical shuffles. For coordinate sweeps with near-uniform line laws and line sizes among powers of two in a suitable fixed interval, we prove a Schatten-moment bound after conditioning on any feasible collection of prescribed card trajectories. An analytic transfer to binary sweeps then shows that a fixed number of sweeps mixes the Thorp shuffle on $`2^d`$ cards in $`O(d)`$ physical steps, matching the order of the support lower bound. We prove a permanent inequality with exponent strictly below two for laws on S4 sufficiently close to uniform and with exactly uniform coordinate marginals. Applied to a four-row recursion, it shows that an absolute number of coordinate sweeps brings the full permutation of the Thorp shuffle on $`N=2^d`$ cards to total-variation distance tending to zero from uniform as $`N\to\infty`$. Thus the mixing time has the optimal order $`O(\log N)`$ in physical shuffles.
- notes: OpenAI math result family 238, Optimal logarithmic mixing of the Thorp shuffle -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/238.md
- track: solved
- answer_shape: proof
- context_lemmas: row_lt_colLen orbit_mem_space action_mem_space switchFun_involutive card_positions
- source_theorem: OAI.CubeShuffle.WeightedSweep.weighted_sweep_moments
- source_theorem_count: 1
- source_solution_module: OAI.Probability.CubeShuffle.WeightedMoments
- source_papers: preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf preprints/From-partial-permutation-information-to-Fourier-bounds-September-26-2026/main.pdf preprints/Conditional-permutations-in-a-revealed-switching-environment-September-26-2026/paper.pdf preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf preprints/Random-subspace-tests-and-trace-smoothing-for-coordinate-sweeps-September-26-2026/paper.pdf preprints/Compatibility-entropy-and-the-spectrum-of-a-Thorp-sweep-September-26-2026/paper.pdf preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf preprints/Conditional-coordinate-sweeps-and-analytic-transfer-September-26-2026/main.pdf preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/main.pdf
- source_scope_note: lean/docs/238.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace CubeShuffle.Specht

open scoped BigOperators Classical

abbrev Cell (μ : YoungDiagram) := {x : ℕ × ℕ // x ∈ μ.cells}
def row {μ : YoungDiagram} (x : Cell μ) : ℕ := x.1.1
def col {μ : YoungDiagram} (x : Cell μ) : ℕ := x.1.2

lemma row_lt_colLen {μ : YoungDiagram} (x : Cell μ) : row x < μ.colLen (col x) :=
  YoungDiagram.mem_iff_lt_colLen.mp x.2
noncomputable def rowIndex {μ : YoungDiagram} (x : Cell μ) : Fin (μ.colLen 0) :=
  ⟨row x, (row_lt_colLen x).trans_le (μ.colLen_anti 0 (col x) (Nat.zero_le _))⟩

abbrev Tabloid (μ : YoungDiagram) :=
  {f : Cell μ → Fin (μ.colLen 0) // ∃ p : Equiv.Perm (Cell μ), f = rowIndex ∘ p}

noncomputable instance (μ : YoungDiagram) : Fintype (Tabloid μ) := Fintype.ofFinite _

noncomputable def baseTabloid (μ : YoungDiagram) : Tabloid μ := ⟨rowIndex, 1, rfl⟩

noncomputable def tabloidAct {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) :
    Equiv.Perm (Tabloid μ) where
  toFun f := ⟨fun x => f.1 (p⁻¹ x), by
    obtain ⟨q,hq⟩ := f.2
    refine ⟨q*p⁻¹, ?_⟩
    funext x
    simp only [hq,Function.comp_apply,Equiv.Perm.mul_apply]⟩
  invFun f := ⟨fun x => f.1 (p x), by
    obtain ⟨q,hq⟩ := f.2
    refine ⟨q*p, ?_⟩
    funext x
    simp only [hq,Function.comp_apply,Equiv.Perm.mul_apply]⟩
  left_inv f := by apply Subtype.ext; funext x; simp
  right_inv f := by apply Subtype.ext; funext x; simp

@[simp] lemma tabloidAct_apply {μ : YoungDiagram} (p : Equiv.Perm (Cell μ))
    (f : Tabloid μ) (x : Cell μ) : (tabloidAct p f).1 x = f.1 (p⁻¹ x) := rfl

@[simp] lemma tabloidAct_one (μ : YoungDiagram) : tabloidAct (1 : Equiv.Perm (Cell μ)) = 1 := by
  ext f x
  rfl

@[simp] lemma tabloidAct_mul {μ : YoungDiagram} (p q : Equiv.Perm (Cell μ)) :
    tabloidAct (p*q) = tabloidAct p * tabloidAct q := by
  ext f x
  simp only [tabloidAct_apply, mul_inv_rev,Equiv.Perm.mul_apply]

@[simp] lemma tabloidAct_inv {μ : YoungDiagram} (p : Equiv.Perm (Cell μ)) :
    tabloidAct p⁻¹ = (tabloidAct p)⁻¹ := by
  ext f x
  simp [tabloidAct,Equiv.Perm.inv_def]

noncomputable def tabloidRep (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (Tabloid μ → ℂ) where
  toFun p :=
    { toFun := fun v f => v (tabloidAct p⁻¹ f)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext v f; simp
  map_mul' p q := by
    ext v f
    simp only [mul_inv_rev,tabloidAct_mul,Equiv.Perm.mul_apply]
    rfl

@[simp] lemma tabloidRep_apply {μ : YoungDiagram} (p : Equiv.Perm (Cell μ))
    (v : Tabloid μ → ℂ) (f : Tabloid μ) : tabloidRep μ p v f = v (tabloidAct p⁻¹ f) := rfl

noncomputable def delta {μ : YoungDiagram} (f : Tabloid μ) : Tabloid μ → ℂ :=
  fun g => if g=f then 1 else 0

noncomputable def colGroup (μ : YoungDiagram) : Subgroup (Equiv.Perm (Cell μ)) where
  carrier := {p | ∀ x, col (p x) = col x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro p q hp hq x; exact (hp (q x)).trans (hq x)
  inv_mem' := by intro p hp x; simpa using (hp (p⁻¹ x)).symm

noncomputable def permSign {α : Type*} [Fintype α] [DecidableEq α] (p : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign p : ℤ) : ℂ)
section Alternator
variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℂ V]

noncomputable def alternator (C : Subgroup (Equiv.Perm α))
    (ρ : Representation ℂ (Equiv.Perm α) V) : Module.End ℂ V := by
  classical
  exact ∑ c : C, permSign (c : Equiv.Perm α) • ρ c

end Alternator

noncomputable def polytabloid (μ : YoungDiagram) : Tabloid μ → ℂ :=
  alternator (colGroup μ) (tabloidRep μ) (delta (baseTabloid μ))

noncomputable def space (μ : YoungDiagram) : Submodule ℂ (Tabloid μ → ℂ) :=
  Submodule.span ℂ (Set.range (fun p : Equiv.Perm (Cell μ) => tabloidRep μ p (polytabloid μ)))

lemma orbit_mem_space (μ : YoungDiagram) (p : Equiv.Perm (Cell μ)) :
    tabloidRep μ p (polytabloid μ) ∈ space μ := Submodule.subset_span ⟨p,rfl⟩

lemma action_mem_space (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (v : Tabloid μ → ℂ) (hv : v ∈ space μ) : tabloidRep μ p v ∈ space μ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q,rfl⟩ := hv
    change ((tabloidRep μ p)*(tabloidRep μ q)) (polytabloid μ) ∈ space μ
    rw [←map_mul]
    exact orbit_mem_space μ (p*q)
  | zero => simp
  | add v w hv hw ihv ihw => simpa using (space μ).add_mem ihv ihw
  | smul a v hv ih => simpa using (space μ).smul_mem a ih

noncomputable def subrepresentation (μ : YoungDiagram) : Subrepresentation (tabloidRep μ) :=
  ⟨space μ, fun p v hv => action_mem_space μ p v hv⟩

noncomputable def representation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (space μ) :=
  (subrepresentation μ).toRepresentation

end CubeShuffle.Specht

namespace CubeShuffle.PermutationHilbert

open scoped BigOperators ComplexConjugate Classical
open Complex

variable {X : Type*} [Fintype X]

abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ X

end CubeShuffle.PermutationHilbert

namespace CubeShuffle.Specht

open scoped BigOperators Classical

noncomputable def hilbertEquiv (μ : YoungDiagram) :
    (Tabloid μ → ℂ) ≃ₗ[ℂ] PermutationHilbert.H (Tabloid μ) :=
  (WithLp.linearEquiv 2 ℂ (Tabloid μ → ℂ)).symm

noncomputable def hilbertSpace (μ : YoungDiagram) :
    Submodule ℂ (PermutationHilbert.H (Tabloid μ)) := (space μ).map (hilbertEquiv μ).toLinearMap

noncomputable def spaceHilbertEquiv (μ : YoungDiagram) : space μ ≃ₗ[ℂ] hilbertSpace μ :=
  (hilbertEquiv μ).submoduleMap (space μ)

noncomputable def unitaryRepresentation (μ : YoungDiagram) :
    Representation ℂ (Equiv.Perm (Cell μ)) (hilbertSpace μ) :=
  ((spaceHilbertEquiv μ).conjAlgEquiv ℂ).toMonoidHom.comp (representation μ)

variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def relabelledUnitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation ℂ (Equiv.Perm α) (hilbertSpace μ) :=
  (unitaryRepresentation μ).comp e.permCongrHom.toMonoidHom

end CubeShuffle.Specht

namespace CubeShuffle

open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

def Coins : ℕ → Type
  | 0 => Unit
  | d + 1 => Card d → Bool

instance (d : ℕ) : Fintype (Coins d) := by
  cases d <;> dsimp [Coins] <;> infer_instance

instance (d : ℕ) : Nonempty (Coins d) := by
  cases d <;> dsimp [Coins] <;> infer_instance

def switchFun {d : ℕ} (ξ : Card d → Bool) (x : Card (d + 1)) : Card (d + 1) :=
  Fin.cons (Bool.xor (x 0) (ξ (Fin.tail x))) (Fin.tail x)

theorem switchFun_involutive {d : ℕ} (ξ : Card d → Bool) :
    Function.Involutive (switchFun ξ) := by
  intro x
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [switchFun, Fin.cons_zero, Fin.tail_cons]
    cases x 0 <;> cases ξ (Fin.tail x) <;> rfl
  · simp [switchFun, Fin.tail]

def pairSwitch {d : ℕ} (ξ : Card d → Bool) : Equiv.Perm (Card (d + 1)) :=
  { toFun := switchFun ξ
    invFun := switchFun ξ
    left_inv := switchFun_involutive ξ
    right_inv := switchFun_involutive ξ }

def rotate (d : ℕ) : Equiv.Perm (Card d) where
  toFun x i := x (finRotate d i)
  invFun x i := x ((finRotate d).symm i)
  left_inv x := by funext i; simp only [Equiv.apply_symm_apply]
  right_inv x := by funext i; simp only [Equiv.symm_apply_apply]

def step : (d : ℕ) → Coins d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, ξ => rotate (d + 1) * pairSwitch ξ

def run (d : ℕ) : (t : ℕ) → (Fin t → Coins d) → Equiv.Perm (Card d)
  | 0, _ => 1
  | t + 1, ω => step d (ω (Fin.last t)) * run d t (fun i => ω i.castSucc)

lemma card_positions (d : ℕ) : Fintype.card (Card d) = 2 ^ d := by
  simp [Card]

end CubeShuffle

namespace CubeShuffle.Specht
open scoped BigOperators Classical

@[simp] lemma card_cell (μ : YoungDiagram) : Fintype.card (Cell μ) = μ.card := by
  simp [Cell, YoungDiagram.card]

abbrev Shapes (N : ℕ) := {μ : YoungDiagram // μ.card = N}

noncomputable def labels {N : ℕ} (μ : Shapes N) : Cell μ.1 ≃ Fin N :=
  (Fintype.equivFin (Cell μ.1)).trans (finCongr ((card_cell μ.1).trans μ.2))

noncomputable def cardLabels (d : ℕ) (μ : Shapes (2^d)) : Card d ≃ Cell μ.1 :=
  ((Fintype.equivFin (Card d)).trans (finCongr (card_positions d))).trans (labels μ).symm

noncomputable def cardRepresentation (d : ℕ) (μ : Shapes (2^d)) :
    Representation ℂ (Equiv.Perm (Card d)) (hilbertSpace μ.1) :=
  relabelledUnitary μ.1 (cardLabels d μ)

end CubeShuffle.Specht

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def continuousRepresentation (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

end CubeShuffle.UnitaryFinite

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sampleOperator (ρ : Representation ℂ G V) (P : Ω → G) : V →L[ℂ] V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,continuousRepresentation ρ (P ω)

end CubeShuffle.UnitaryFinite

noncomputable section
open scoped BigOperators Classical

namespace CubeShuffle.WeightedSweep
open Specht UnitaryFinite

def dimension (μ : YoungDiagram) : ℝ := Module.finrank ℂ (space μ)
def fourierSweep (d : ℕ) (μ : Shapes (2^d)) :
    hilbertSpace μ.1 →L[ℂ] hilbertSpace μ.1 :=
  sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d d)
def schattenMoment {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →L[ℂ] V) (p : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℂ V), (A.toLinearMap.singularValues i) ^ p

def schattenNorm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →L[ℂ] V) (p : ℝ) : ℝ :=
  schattenMoment A p ^ (1 / p)

end CubeShuffle.WeightedSweep

end

noncomputable section
open scoped BigOperators Classical

namespace CubeShuffle.WeightedSweep
open Specht UnitaryFinite

def weighted_sweep_moments_statement : Prop :=
  ∃ (W : YoungDiagram → ℝ) (pStar : ℝ) (p : ℕ → ℝ),
      (∀ μ : YoungDiagram, 0 < W μ) ∧
      2 ≤ pStar ∧
      (∀ d : ℕ, 1 ≤ d → 2 ≤ p d ∧ p d ≤ pStar) ∧
      ∀ d : ℕ, 1 ≤ d → ∀ μ : Shapes (2 ^ d),
        dimension μ.1 ^ (3 / 4 : ℝ) ≤ W μ.1 ∧
        W μ.1 ≤ dimension μ.1 ∧
        W μ.1 *
          schattenNorm (V := hilbertSpace μ.1) (fourierSweep d μ) (p d) ^ (p d) ≤ 1 ∧
        ‖fourierSweep d μ‖ ≤ dimension μ.1 ^ (-3 / (4 * pStar))

end CubeShuffle.WeightedSweep

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CubeShuffle.WeightedSweep.weighted_sweep_moments_statement

end Problem

/- Formalization scope, from lean/docs/238.md: The formalization proves optimal-order mixing of the Thorp shuffle on $2^d$ cards. After $1600d$ complete shuffles, the full permutation law converges in total variation to uniform as $d\to\infty$, uniformly over initial decks. Together with the support lower bound of $2d-O(1)$, this gives mixing time $\Theta(d)=\Theta(\log(2^d))$. The linked supporting results include frame and conditional-list estimates, regular trace and spectral bounds, signed moments, and full-density $L^2$ control. They also bound reciprocal Specht-dimension sums and give the eight-block Fourier estimate used in the mixing argument. The formalized supporting result turns bounds on partial-permutation cosets into Fourier bounds. Partition a finite set into $b\ge1$ nonempty blocks, and let $f\ge0$ be a subprobability weight on its symmetric group whose left-coset masses for each block subgroup are at most $B$. For every irreducible unitary representation of dimension $D$ and every $u>0$, both the squared Hilbert–Schmidt norm and squared operator norm of its Fourier transform are at most $bB\,C(u)D^{-1+(u+2)/b}$, where $C(u)$ is the stated symmetric-group degree constant. The paper's asymptotic conclusion about the product of two random permutations is outside this selected finite estimate. The formalized results give averaged conditional mixing for half-permutations in the revealed-path model and full-deck mixing for the Thorp shuffle. In particular, the full-deck total-variation distance tends to zero after $16040400d$ steps on $2^d$ cards, uniformly over deterministic initial decks. The conditional estimate is averaged over the actual outside-path law, rather than asserted for each individual environment. The formalization also includes the associated overlay, reset minorization, and two-color conditional constructions. The formalization covers nine routing and representation estimates for Thorp sweeps: adaptive operator and fourth-trace bounds, Casimir moments, dense truncation, sparse contact, harmonic-cycle contraction, smoothing, and three tail or sparse-saving estimates. They bound routing-density deviations and Fourier operators in dense and sparse regimes, including exponential savings in the level scale and representation dimension. The conditional high-height estimate requires a sufficiently large cutoff height $J$ that exceeds twice the number $s$ of coordinates in the fixed low block, so $J>2s$. These are the earlier nine statements associated with the paper; its changed later statements and six other result blocks are outside this scope. The formalization proves uniform representation bounds for one coordinate sweep of the Thorp shuffle. For each irreducible representation of dimension $D$, it chooses a weight between $D^{3/4}$ and $D$ and a Schatten exponent bounded by one absolute constant so that the weighted Schatten moment is at most one. The sweep's operator norm is consequently at most $D^{-c}$ for one absolute $c>0$. The supporting row–column estimate bounds the total squared overlap over all multiplicity copies on an occupied board, with explicit dependence on the row and column representation dimensions, the global dimension, the number of missing cells, and the number of rows or columns containing the global Young diagram. The paper's full physical-mixing conclusion is outside these selected representation estimates. The formalization proves a uniform trace-smoothing estimate for coordinate sweeps of the Thorp shuffle on $2^d$ cards. One absolute sweep parameter works for every $d\ge1$: the regular trace is at most $1+(2^d)^{-10}$, and the full permutation law after the corresponding fixed number of sweeps is within $\tfrac12(2^d)^{-5}$ of uniform in total variation, for every initial deck. Thus the selected upper bound uses $O(d)$ physical shuffles. The formalized result is the weighted compatibility theorem for balanced $A\times D$ rectangles, with $n=AD$ and $\sqrt n/2\le A,D\le2\sqrt n$. For arbitrary nonnegative weights on the row and column permutation groups, the normalized compatibility average is bounded by $\exp(C_0n^{54/100})$ times the product of the marginal $L^{1/\theta}$ factors, where $\theta=1-L/\log\sqrt n>0$ and the constants are absolute. Compatibility means injectivity in every original column. The bounded regular-moment and other moment/rank conclusions are not included. The formalization gives signed representation estimates for coordinate sweeps of the Thorp shuffle. For every signed occurrence of a Young diagram of size $2^d$, it bounds the logarithm of a fixed-order weighted sweep moment by a small multiple of the signed partition entropy plus an explicit remainder-size budget. The moment order is uniform over the diagrams and decompositions after the two small coefficients are fixed. The linked supporting angle bound controls the overlap of row, column, and global signed-type projections on an occupied rectangle, with explicit entropy, dimension, and missing-cell factors. These selected estimates support the paper's full-density argument; the full $L^2$ and total-variation mixing conclusion is outside them. The formalized binary-sweep theorem gives a universal power contraction in every irreducible representation: for sufficiently large $d$, the averaged sweep on $2^d$ slots has operator norm at most $D^{-g}$ in representation dimension $D$, for some $g>0$. The sign expectation is zero, and a fixed number of independent sweeps approaches uniform in total variation from every initial deck. A separate conditional moment estimate covers allowed power-of-two grids and disjoint coordinate-respecting trajectories, with its stated feasibility premise. Physical-shuffle law identification is not included. The formalization proves the paper's strict four-row permanent inequality. There are constants $4/3<p<2$ and $\varepsilon>0$ such that every probability law on $S_4$ within total-variation distance $\varepsilon$ of uniform, and with exactly uniform coordinate marginals, satisfies the permanent bound by the product of the four $L^p$ row norms for every nonnegative matrix. The exponent and neighborhood are uniform over those laws. The Thorp mixing consequence is outside this selected statement. -/
