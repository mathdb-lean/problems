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

- problem_id: ThorpFirstReciprocal
- collection: openai-math
- question_id: openai-math:238
- source: openai-math
- source_locator: lean/ComparatorChallenges/ThorpFirstReciprocal.lean#OAI.Thorp.Current.first_reciprocal_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that the Thorp shuffle randomizes $`N=2^d`$ labeled cards in $`\Theta(\log N)`$ physical shuffles, settling its optimal mixing order for power-of-two deck sizes. Convergence is in total variation from the worst initial ordering and concerns the entire permutation, not just individual card positions. ([Lean](lean/docs/238.md)) We prove that the Thorp shuffle on $`2^d`$ cards mixes in $`\Theta(d)`$ complete shuffles. The full permutation law after $`1600d`$ shuffles converges to uniform in total variation as $`d\to\infty`$, uniformly over the initial deck, while a support count gives a lower bound of $`2d-O(1)`$. We show how information about partial permutations controls full permutation laws. Let n tend to infinity through multiples of eight. If the images of a uniformly chosen $`7n/8`$ labels approach the uniform injection law in average total variation, and the sign mean tends to zero, then the product of two independent permutations with the given law converges to uniform on Sn. Fix half the labels in a Thorp shuffle on $`2^d`$ positions and reveal their complete trajectories. We prove that, after an explicit absolute number of coordinate sweeps, the conditional permutation of the remaining labels approaches uniform in expected total variation as $`d\to\infty`$, uniformly in the initial layout. The resulting constructions give full-deck mixing in a constant multiple of d physical shuffles. For $`N=2^d`$ cards, we prove that an absolute number of coordinate sweeps of the Thorp shuffle brings the full permutation law to total-variation distance tending to zero from uniform. The mixing time therefore has optimal order $`\Theta(\log N)`$ in physical shuffles. We prove that the Thorp shuffle on $`N=2^d`$ labeled cards has full-permutation total-variation mixing time $`\Theta(\log N)`$ in physical shuffles. An absolute number of coordinate sweeps suffices for the upper bound. We prove that an absolute number of coordinate sweeps of the Thorp shuffle on $`n=2^d`$ positions brings the full permutation to total-variation distance at most $`\frac12n^{-5}`$ from uniform, uniformly over the initial deck. Thus $`O(d)`$ physical shuffles suffice, which is optimal in order. We prove that the Thorp shuffle on $`n=2^d`$ cards mixes in $`\Theta(d)`$ physical shuffles. After a sufficiently large fixed number of coordinate sweeps, the total-variation distance of the full permutation from uniform tends to zero as $`d\to\infty`$. We prove that a fixed number of coordinate sweeps of the Thorp shuffle on $`2^d`$ cards makes the squared L2 distance of the full permutation density from uniform tend to zero as $`d\to\infty`$. In particular, the total-variation mixing time is $`\Theta(d)`$ physical shuffles. For coordinate sweeps with near-uniform line laws and line sizes among powers of two in a suitable fixed interval, we prove a Schatten-moment bound after conditioning on any feasible collection of prescribed card trajectories. An analytic transfer to binary sweeps then shows that a fixed number of sweeps mixes the Thorp shuffle on $`2^d`$ cards in $`O(d)`$ physical steps, matching the order of the support lower bound. We prove a permanent inequality with exponent strictly below two for laws on S4 sufficiently close to uniform and with exactly uniform coordinate marginals. Applied to a four-row recursion, it shows that an absolute number of coordinate sweeps brings the full permutation of the Thorp shuffle on $`N=2^d`$ cards to total-variation distance tending to zero from uniform as $`N\to\infty`$. Thus the mixing time has the optimal order $`O(\log N)`$ in physical shuffles.
- notes: OpenAI math result family 238, Optimal logarithmic mixing of the Thorp shuffle -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/238.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Thorp.Current.first_reciprocal_main
- source_theorem_count: 1
- source_solution_module: OAI.Probability.ThorpShuffle.FirstMain
- source_papers: preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf preprints/From-partial-permutation-information-to-Fourier-bounds-September-26-2026/main.pdf preprints/Conditional-permutations-in-a-revealed-switching-environment-September-26-2026/paper.pdf preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf preprints/Random-subspace-tests-and-trace-smoothing-for-coordinate-sweeps-September-26-2026/paper.pdf preprints/Compatibility-entropy-and-the-spectrum-of-a-Thorp-sweep-September-26-2026/paper.pdf preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf preprints/Conditional-coordinate-sweeps-and-analytic-transfer-September-26-2026/main.pdf preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/main.pdf
- source_scope_note: lean/docs/238.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

universe uG uV uE uX uH uI uβ uα

open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

abbrev Position (d : ℕ) := Fin d → Bool

namespace Block

variable {I : Type uI} {β : Type uβ} {α : Type uα}

def perm (p : I → Equiv.Perm β) : Equiv.Perm (I × β) where
  toFun x := (x.1, p x.1 x.2)
  invFun x := (x.1, (p x.1)⁻¹ x.2)
  left_inv x := by simp
  right_inv x := by simp

def hom : (I → Equiv.Perm β) →* Equiv.Perm (I × β) where
  toFun := perm
  map_one' := by ext ⟨i,b⟩ <;> rfl
  map_mul' p q := by ext ⟨i,b⟩ <;> rfl

def embedding (e : α ≃ I × β) : (I → Equiv.Perm β) →* Equiv.Perm α :=
  (e.symm.permCongrHom).toMonoidHom.comp hom

end Block

namespace Fourier

variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

def integrated (ρ : Representation ℂ G V) (f : G → ℂ) : Module.End ℂ V :=
  ∑ g, f g • ρ g

end Fourier

namespace Young

abbrev Cells (D : YoungDiagram) := {p : ℕ × ℕ // p ∈ D.cells}

def rowCellsEquiv (D : YoungDiagram) : Cells D ≃ (i : Fin (D.colLen 0)) × Fin (D.rowLen i) where
  toFun x := ⟨⟨x.val.1, YoungDiagram.mem_iff_lt_colLen.mp (D.up_left_mem le_rfl (Nat.zero_le _) x.property)⟩,
    ⟨x.val.2, YoungDiagram.mem_iff_lt_rowLen.mp x.property⟩⟩
  invFun x := ⟨(x.1, x.2), YoungDiagram.mem_iff_lt_rowLen.mpr x.2.isLt⟩
  left_inv x := rfl
  right_inv x := by cases x; rfl

def ofPartition {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

def longest (D : YoungDiagram) : ℕ := max (D.rowLen 0) (D.colLen 0)

end Young

namespace Specht

variable {G : Type uG} [Group G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def cyclic (ρ : Representation ℂ G E) (e : E) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g e)
  apply_mem_toSubmodule g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h, rfl⟩ := hv
      exact Submodule.subset_span ⟨g * h, by simp⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).add_mem ihx ihy
    | smul a x hx ih =>
      simpa using (Submodule.span ℂ (Set.range fun h => ρ h e)).smul_mem a ih

namespace PermutationSpace

variable {X : Type uX} [Fintype X] [MulAction G X]

def rep : Representation ℂ G (EuclideanSpace ℂ X) where
  toFun g := {
    toFun v := WithLp.toLp 2 (fun x => v (g⁻¹ • x))
    map_add' := by intro v w; rfl
    map_smul' := by intro a v; rfl }
  map_one' := by ext v x; simp
  map_mul' := by
    intro g h
    ext v x
    change v ((g * h)⁻¹ • x) = v (h⁻¹ • g⁻¹ • x)
    simp [mul_smul]

variable {H : Type uH} [Group H] [Fintype H]

def alternator (ι : H →* G) (χ : H →* ℂ) : Module.End ℂ (EuclideanSpace ℂ X) :=
  ∑ h, χ h • rep (ι h)

end PermutationSpace

variable {α : Type uα} [Fintype α]

def Tabloid (r : α → ℕ) := {f : α → ℕ // ∃ g : Equiv.Perm α, f = r ∘ g}

instance tabloidFinite (r : α → ℕ) : Finite (Tabloid r) := by
  apply Finite.of_surjective (fun g : Equiv.Perm α => (⟨r ∘ g, g, rfl⟩ : Tabloid r))
  rintro ⟨f, g, rfl⟩
  exact ⟨g, rfl⟩

instance tabloidFintype (r : α → ℕ) : Fintype (Tabloid r) := Fintype.ofFinite _

instance tabloidAction (r : α → ℕ) : MulAction (Equiv.Perm α) (Tabloid r) where
  smul g f := ⟨f.val ∘ ⇑(g⁻¹ : Equiv.Perm α), by
    obtain ⟨h, hh⟩ := f.property
    refine ⟨h * g⁻¹, ?_⟩
    funext x
    simp only [Function.comp_apply, hh, Equiv.Perm.mul_apply]⟩
  one_smul f := by apply Subtype.ext; funext x; rfl
  mul_smul g h f := by
    apply Subtype.ext
    funext x
    change f.val ((g * h)⁻¹ x) = f.val (h⁻¹ (g⁻¹ x))
    rw [mul_inv_rev, Equiv.Perm.mul_apply]

def baseTabloid (r : α → ℕ) : Tabloid r := ⟨r, 1, by funext x; rfl⟩

def fiberGroup (c : α → ℕ) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, c (g x) = c x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro g h hg hh x; exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have hh := hg (g⁻¹ x)
    change c (g (g.symm x)) = c (g.symm x) at hh
    rw [g.apply_symm_apply] at hh
    exact hh.symm

def complexSign : Equiv.Perm α →* ℂ where
  toFun g := ((Equiv.Perm.sign g : ℤˣ) : ℤ)
  map_one' := by simp
  map_mul' := by intro g h; simp

variable (D : YoungDiagram) (t : α ≃ Thorp.Young.Cells D)

def tableauRow (x : α) : ℕ := (t x).val.1

def tableauCol (x : α) : ℕ := (t x).val.2

def tabloidRep : Representation ℂ (Equiv.Perm α) (EuclideanSpace ℂ (Tabloid (tableauRow D t))) :=
  PermutationSpace.rep

def columnAlternator : Module.End ℂ (EuclideanSpace ℂ (Tabloid (tableauRow D t))) :=
  PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)

def polytabloid : EuclideanSpace ℂ (Tabloid (tableauRow D t)) :=
  columnAlternator D t (EuclideanSpace.single (baseTabloid (tableauRow D t)) (1 : ℂ))

def module : Subrepresentation (tabloidRep D t) := cyclic (tabloidRep D t) (polytabloid D t)

abbrev Shape (α : Type uα) [Fintype α] := Nat.Partition (Fintype.card α)

def canonicalTableau (p : Shape α) : α ≃ Thorp.Young.Cells (Thorp.Young.ofPartition p) := by
  have card_cells_eq_sum (D : YoungDiagram) : Fintype.card (Thorp.Young.Cells D) = D.rowLens.sum := by
    rw [Fintype.card_congr (Thorp.Young.rowCellsEquiv D), Fintype.card_sigma]
    simp only [Fintype.card_fin, YoungDiagram.rowLens]
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]
  have rowLens_ofPartition {n : ℕ} (p : Nat.Partition n) :
      (Thorp.Young.ofPartition p).rowLens = p.parts.sort (· ≥ ·) := by
    apply YoungDiagram.rowLens_ofRowLens_eq_self
    intro x hx
    exact p.parts_pos ((Multiset.mem_sort _).mp hx)
  have card_ofPartition {n : ℕ} (p : Nat.Partition n) : Fintype.card (Thorp.Young.Cells (Thorp.Young.ofPartition p)) = n := by
    rw [card_cells_eq_sum, rowLens_ofPartition]
    simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum
  exact Fintype.equivOfCardEq (card_ofPartition p).symm

abbrev Space (p : Shape α) := (module (Thorp.Young.ofPartition p) (canonicalTableau p)).toSubmodule

def degree (p : Shape α) : ℕ := Module.finrank ℂ (Space p)

open Thorp.Young

abbrev NShape (n : ℕ) := Shape (Fin n)

def defect {n : ℕ} (p : NShape n) : ℕ := n - longest (ofPartition p)

end Specht

namespace Current

def reciprocalFirst (n : ℕ) : ℝ :=
  ∑ p : Specht.NShape n, (Specht.degree p : ℝ)⁻¹

def exceptionalFirst (n : ℕ) : ℝ :=
  ∑ p : Specht.NShape n, if 0 < Specht.defect p then (Specht.degree p : ℝ)⁻¹ else 0

def C1 : ℝ := sSup (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val))

def first_reciprocal_main_statement : Prop :=
  (BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) ∧
    (∀ n : ℕ, 1 ≤ n → reciprocalFirst n ≤ C1) ∧
    Tendsto exceptionalFirst atTop (nhds 0)) ∧
    (∀ (d : ℕ) (_hd : 3 ≤ d)
    (e : Position d ≃ Fin 8 × Fin (2 ^ (d - 3)))
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (Equiv.Perm (Position d)) E)
    [Representation.IsIrreducible ρ]
    (_ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ν : Equiv.Perm (Position d) → ℝ)
    (_ : ∀ g, 0 ≤ ν g) (_ : ∑ g, ν g = 1)
    (_ : ∀ (i : Fin 8) (g : Equiv.Perm (Position d)),
      ∑ h : Equiv.Perm (Fin (2 ^ (d - 3))),
          ν (g * Block.embedding e (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin (2 ^ (d - 3)))) : ℝ) /
          Fintype.card (Equiv.Perm (Position d))),
    ‖LinearMap.toContinuousLinearMap (Fourier.integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ))

end Current

end Thorp

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{uE} : Prop :=
  _root_.OAI.Thorp.Current.first_reciprocal_main_statement.{uE}

end Problem

/- Formalization scope, from lean/docs/238.md: The formalization proves optimal-order mixing of the Thorp shuffle on $2^d$ cards. After $1600d$ complete shuffles, the full permutation law converges in total variation to uniform as $d\to\infty$, uniformly over initial decks. Together with the support lower bound of $2d-O(1)$, this gives mixing time $\Theta(d)=\Theta(\log(2^d))$. The linked supporting results include frame and conditional-list estimates, regular trace and spectral bounds, signed moments, and full-density $L^2$ control. They also bound reciprocal Specht-dimension sums and give the eight-block Fourier estimate used in the mixing argument. The formalized supporting result turns bounds on partial-permutation cosets into Fourier bounds. Partition a finite set into $b\ge1$ nonempty blocks, and let $f\ge0$ be a subprobability weight on its symmetric group whose left-coset masses for each block subgroup are at most $B$. For every irreducible unitary representation of dimension $D$ and every $u>0$, both the squared Hilbert–Schmidt norm and squared operator norm of its Fourier transform are at most $bB\,C(u)D^{-1+(u+2)/b}$, where $C(u)$ is the stated symmetric-group degree constant. The paper's asymptotic conclusion about the product of two random permutations is outside this selected finite estimate. The formalized results give averaged conditional mixing for half-permutations in the revealed-path model and full-deck mixing for the Thorp shuffle. In particular, the full-deck total-variation distance tends to zero after $16040400d$ steps on $2^d$ cards, uniformly over deterministic initial decks. The conditional estimate is averaged over the actual outside-path law, rather than asserted for each individual environment. The formalization also includes the associated overlay, reset minorization, and two-color conditional constructions. The formalization covers nine routing and representation estimates for Thorp sweeps: adaptive operator and fourth-trace bounds, Casimir moments, dense truncation, sparse contact, harmonic-cycle contraction, smoothing, and three tail or sparse-saving estimates. They bound routing-density deviations and Fourier operators in dense and sparse regimes, including exponential savings in the level scale and representation dimension. The conditional high-height estimate requires a sufficiently large cutoff height $J$ that exceeds twice the number $s$ of coordinates in the fixed low block, so $J>2s$. These are the earlier nine statements associated with the paper; its changed later statements and six other result blocks are outside this scope. The formalization proves uniform representation bounds for one coordinate sweep of the Thorp shuffle. For each irreducible representation of dimension $D$, it chooses a weight between $D^{3/4}$ and $D$ and a Schatten exponent bounded by one absolute constant so that the weighted Schatten moment is at most one. The sweep's operator norm is consequently at most $D^{-c}$ for one absolute $c>0$. The supporting row–column estimate bounds the total squared overlap over all multiplicity copies on an occupied board, with explicit dependence on the row and column representation dimensions, the global dimension, the number of missing cells, and the number of rows or columns containing the global Young diagram. The paper's full physical-mixing conclusion is outside these selected representation estimates. The formalization proves a uniform trace-smoothing estimate for coordinate sweeps of the Thorp shuffle on $2^d$ cards. One absolute sweep parameter works for every $d\ge1$: the regular trace is at most $1+(2^d)^{-10}$, and the full permutation law after the corresponding fixed number of sweeps is within $\tfrac12(2^d)^{-5}$ of uniform in total variation, for every initial deck. Thus the selected upper bound uses $O(d)$ physical shuffles. The formalized result is the weighted compatibility theorem for balanced $A\times D$ rectangles, with $n=AD$ and $\sqrt n/2\le A,D\le2\sqrt n$. For arbitrary nonnegative weights on the row and column permutation groups, the normalized compatibility average is bounded by $\exp(C_0n^{54/100})$ times the product of the marginal $L^{1/\theta}$ factors, where $\theta=1-L/\log\sqrt n>0$ and the constants are absolute. Compatibility means injectivity in every original column. The bounded regular-moment and other moment/rank conclusions are not included. The formalization gives signed representation estimates for coordinate sweeps of the Thorp shuffle. For every signed occurrence of a Young diagram of size $2^d$, it bounds the logarithm of a fixed-order weighted sweep moment by a small multiple of the signed partition entropy plus an explicit remainder-size budget. The moment order is uniform over the diagrams and decompositions after the two small coefficients are fixed. The linked supporting angle bound controls the overlap of row, column, and global signed-type projections on an occupied rectangle, with explicit entropy, dimension, and missing-cell factors. These selected estimates support the paper's full-density argument; the full $L^2$ and total-variation mixing conclusion is outside them. The formalized binary-sweep theorem gives a universal power contraction in every irreducible representation: for sufficiently large $d$, the averaged sweep on $2^d$ slots has operator norm at most $D^{-g}$ in representation dimension $D$, for some $g>0$. The sign expectation is zero, and a fixed number of independent sweeps approaches uniform in total variation from every initial deck. A separate conditional moment estimate covers allowed power-of-two grids and disjoint coordinate-respecting trajectories, with its stated feasibility premise. Physical-shuffle law identification is not included. The formalization proves the paper's strict four-row permanent inequality. There are constants $4/3<p<2$ and $\varepsilon>0$ such that every probability law on $S_4$ within total-variation distance $\varepsilon$ of uniform, and with exactly uniform coordinate marginals, satisfies the permanent bound by the product of the four $L^p$ row norms for every nonnegative matrix. The exponent and neighborhood are uniform over those laws. The Thorp mixing consequence is outside this selected statement. -/
