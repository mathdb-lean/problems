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

- problem_id: UniversalTensorSquares
- collection: openai-math
- question_id: openai-math:205
- source: openai-math
- source_locator: lean/ComparatorChallenges/UniversalTensorSquares.lean#OAI.UniversalTensorSquares.universal_tensor_square
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Saxl's conjecture: the tensor square of every staircase representation contains every irreducible complex representation of the corresponding symmetric group. More generally, every Sn with $`n\notin\{2,4,9\}`$ has an irreducible representation whose tensor square contains all irreducibles. ([Lean](lean/docs/205.md)) For every positive integer n other than 2, 4, and 9, we prove that some irreducible complex representation of Sn has a tensor square containing every irreducible representation. This resolves the tensor square conjecture for symmetric groups affirmatively. For every staircase partition, we prove that the tensor square of the corresponding irreducible complex representation of the symmetric group contains every irreducible representation of that group. This proves Saxl's conjecture.
- notes: OpenAI math result family 205, Saxl’s conjecture and universal tensor squares -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/205.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.UniversalTensorSquares.universal_tensor_square
- source_theorem_count: 1
- source_solution_module: OAI.RepresentationTheory.UniversalSquare.Main
- source_papers: preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf preprints/A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026/paper.pdf
- source_scope_note: lean/docs/205.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Universal tensor squares of irreducible complex symmetric-group representations. -/

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

abbrev WordSpace (n d : ℕ) := (Fin n → Fin d) → ℂ

def wordRep (n d : ℕ) : Representation ℂ (Equiv.Perm (Fin n)) (WordSpace n d) where
  toFun g :=
    { toFun := fun f a => f (a ∘ g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f a; rfl
  map_mul' g h := by ext f a; rfl

def cyclic {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g : G => ρ g v)
  apply_mem_toSubmodule g := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨g * h, by simp only [map_mul, Module.End.mul_apply]⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      simpa only [map_smul] using Submodule.smul_mem _ a ih

abbrev Tableau (n : ℕ) (μ : YoungDiagram) := Fin n ≃ μ.cells

def canonicalTableau {n : ℕ} (μ : YoungDiagram) (hn : μ.card = n) : Tableau n μ :=
  (Fintype.equivFinOfCardEq (by simpa using hn)).symm

def rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) : Fin n → Fin (μ.colLen 0) :=
  fun i => ⟨(t i).val.1, YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (Nat.zero_le _) (t i).property)⟩

def columnGroup {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, (t (g i)).val.2 = (t i).val.2}
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro g h hg hh i
    exact (hg (h i)).trans (hh i)
  inv_mem' := by
    intro g hg i
    have h := hg (g⁻¹ i)
    simpa using h.symm

def polytabloid {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    WordSpace n (μ.colLen 0) := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t,
    (((Equiv.Perm.sign (g : Equiv.Perm (Fin n))) : ℤ) : ℂ) •
      wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1)

def spechtSub {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :=
  cyclic (wordRep n (μ.colLen 0)) (polytabloid t)

abbrev Specht {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :=
  (spechtSub t).toSubmodule

def spechtRep {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation ℂ (Equiv.Perm (Fin n)) (Specht t) :=
  (spechtSub t).toRepresentation

def kronecker {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) : ℕ :=
  Module.finrank ℂ (Representation.IntertwiningMap (spechtRep t)
    ((spechtRep a).tprod (spechtRep b)))

end Saxl

namespace UniversalTensorSquares

universe u

def universal_tensor_square_statement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9),
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
          (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
            (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
          Function.Injective F

end UniversalTensorSquares

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.UniversalTensorSquares.universal_tensor_square_statement.{u}

end Problem

/- Formalization scope, from lean/docs/205.md: The formalization proves the universal tensor-square conjecture for symmetric groups in the stated range. For every positive integer $n\notin\{2,4,9\}$, it constructs an irreducible complex representation of $S_n$ whose tensor square contains every irreducible complex representation of $S_n$. Equivalently, all corresponding Kronecker coefficients are positive. The statement also supplies injective intertwining maps for arbitrary finite-dimensional irreducible representations. Saxl's conjecture asserts that the tensor square of each staircase Specht module contains every irreducible representation of the corresponding symmetric group. The formalization establishes this for every $m\ge1$: if $\rho_m=(m,m-1,\ldots,1)$, then $g(\rho_m,\rho_m,\mu)>0$ for every partition $\mu$ of $m(m+1)/2$. The stronger claim that every constituent appears in the orbit span of one prescribed tensor is not included. -/
