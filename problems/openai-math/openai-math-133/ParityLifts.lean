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

- problem_id: ParityLifts
- collection: openai-math
- question_id: openai-math:133
- source: openai-math
- source_locator: lean/ComparatorChallenges/ParityLifts.lean#OAI.ParityWL.parity_reduction
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves unconditional $`n^{\Omega(k)}`$ deterministic time lower bounds for joint and separate k-dimensional Weisfeiler–Leman equivalence, for sufficiently large fixed k in the specified sequential adjacency-matrix models. With dimension as input, joint equivalence is EXPTIME-complete even on subcubic graphs; deciding whether refinement identifies a graph is also EXPTIME-complete. ([Lean](lean/docs/133.md)) For k ≥ 4, we construct two uncolored graphs that are k-dimensional Weisfeiler–Leman equivalent exactly when a prescribed finite-domain choice system has no compatible choice. The system has $`k+1`$ domains for joint refinement and k for separate-coordinate refinement. A successful choice is detected after two joint rounds or one separate round. Applied to sparse satisfiability, the reduction gives fixed-dimension $`n^{\Omega(k)}`$ time exclusions under positive-rate ETH, even for deciding equality of these early histograms. We prove that deciding whether Weisfeiler–Leman refinement of an input dimension identifies a given graph is EXPTIME-complete. The input is a nonempty finite simple uncolored graph in adjacency-matrix form and a positive binary-encoded dimension. Identification quantifies over every comparison graph. For every sufficiently large fixed k, deciding whether two n-vertex graphs are k-Weisfeiler–Leman equivalent requires $`n^{\Omega(k)}`$ deterministic sequential time in the worst case. The bound holds at every sufficiently large graph order, even for simple connected uncolored graphs of diameter at most two, without a complexity assumption. Inputs are explicit adjacency matrices; the models are multitape Turing machines and sequential logarithmic-word RAMs with fixed polynomial-bit-time instructions. Both joint and separate replacement conventions are covered. Deciding joint-update k-dimensional Weisfeiler–Leman equivalence is $`\mathsf{EXPTIME}`$-complete when the two graphs are given by explicit adjacency matrices and k ≥ 2 is encoded in binary. The result holds even for connected simple uncolored graphs of equal positive order and maximum degree at most three.
- notes: OpenAI math result family 133, The computational complexity of Weisfeiler–Leman refinement -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/133.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ParityWL.parity_reduction
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.ParityLifts.Main
- source_papers: preprints/Parity-lifts-and-bounded-treewidth-witnesses-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf preprints/The-complexity-of-identifying-a-graph-by-Weisfeiler-Leman-refinement-September-25-2026/paper.pdf preprints/Unconditional-time-lower-bounds-for-Weisfeiler-Leman-equivalence-September-25-2026/paper.pdf preprints/Variable-dimension-Weisfeiler-Leman-equivalence-on-general-and-subcubic-graphs-September-25-2026/paper.pdf
- source_scope_note: lean/docs/133.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI



namespace ParityWL

open scoped BigOperators

abbrev Bit := ZMod 2
abbrev MainPair (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}
abbrev Helper (t : ℕ) :=
  {q : MainPair t × Fin t // q.2 ≠ q.1.1.1 ∧ q.2 ≠ q.1.1.2}
abbrev TemplateVertex (t : ℕ) := Fin t ⊕ Helper t

structure ChoiceSystem (t : ℕ) where
  Domain : Fin t → Type
  domainFintype : ∀ i, Fintype (Domain i)
  Label : MainPair t → Type
  labelFintype : ∀ p, Fintype (Label p)
  leftLabel : (p : MainPair t) → Domain p.1.1 → Label p
  rightLabel : (p : MainPair t) → Domain p.1.2 → Label p

attribute [instance] ChoiceSystem.domainFintype ChoiceSystem.labelFintype

def ChoiceSystem.Successful {t : ℕ} (C : ChoiceSystem t) : Prop :=
  ∃ d : (i : Fin t) → C.Domain i,
    ∀ p : MainPair t, C.leftLabel p (d p.1.1) = C.rightLabel p (d p.1.2)

def ChoiceSystem.SizeAtMost {t : ℕ} (C : ChoiceSystem t) (A : ℕ) : Prop :=
  (∀ i, Fintype.card (C.Domain i) ≤ A) ∧ (∀ p, Fintype.card (C.Label p) ≤ A)

def helperIncident {t : ℕ} (h : Helper t) (i : Fin t) : Prop :=
  i = h.1.1.1.1 ∨ i = h.1.1.1.2 ∨ i = h.1.2

def templateAdj {t : ℕ} : TemplateVertex t → TemplateVertex t → Prop
  | .inl i, .inl j => i ≠ j
  | .inl i, .inr h => helperIncident h i
  | .inr h, .inl i => helperIncident h i
  | .inr _, .inr _ => False

def template (t : ℕ) : SimpleGraph (TemplateVertex t) where
  Adj := templateAdj
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp_all [templateAdj, ne_comm]⟩
  loopless := ⟨by
    intro x
    cases x <;> simp [templateAdj]⟩

abbrev BaseVertex {t : ℕ} (C : ChoiceSystem t) :=
  ((i : Fin t) × C.Domain i) ⊕ ((h : Helper t) × C.Label h.1.1)

def baseType {t : ℕ} {C : ChoiceSystem t} : BaseVertex C → TemplateVertex t
  | .inl x => .inl x.1
  | .inr x => .inr x.1

inductive BaseArc {t : ℕ} (C : ChoiceSystem t) : BaseVertex C → BaseVertex C → Prop
  | main (p : MainPair t) (d : C.Domain p.1.1) (e : C.Domain p.1.2)
      (h : C.leftLabel p d = C.rightLabel p e) :
      BaseArc C (.inl ⟨p.1.1, d⟩) (.inl ⟨p.1.2, e⟩)
  | left (h : Helper t) (d : C.Domain h.1.1.1.1) :
      BaseArc C (.inr ⟨h, C.leftLabel h.1.1 d⟩) (.inl ⟨h.1.1.1.1, d⟩)
  | right (h : Helper t) (e : C.Domain h.1.1.1.2) :
      BaseArc C (.inr ⟨h, C.rightLabel h.1.1 e⟩) (.inl ⟨h.1.1.1.2, e⟩)
  | third (h : Helper t) (q : C.Label h.1.1) (f : C.Domain h.1.2) :
      BaseArc C (.inr ⟨h, q⟩) (.inl ⟨h.1.2, f⟩)

def baseGraph {t : ℕ} (C : ChoiceSystem t) : SimpleGraph (BaseVertex C) :=
  SimpleGraph.fromRel (BaseArc C)

def baseProjection {t : ℕ} (C : ChoiceSystem t) : baseGraph C →g template t where
  toFun := baseType
  map_rel' := by
    intro x y h
    have arc : ∀ u v, BaseArc C u v → (template t).Adj (baseType u) (baseType v) := by
      intro u v huv
      cases huv with
      | main p d e he => exact ne_of_lt p.property
      | left h d => exact Or.inl rfl
      | right h e => exact Or.inr (Or.inl rfl)
      | third h q f => exact Or.inr (Or.inr rfl)
    rcases h.2 with hxy | hyx
    · exact arc x y hxy
    · exact (arc y x hyx).symm

section Lifts

variable {A V : Type} [Fintype A] (T : SimpleGraph A) (G : SimpleGraph V)

noncomputable def Tag (b : A → Bit) (a : A) := by
  classical
  exact {z : T.neighborSet a → Bit // ∑ v, z v = b a}

noncomputable instance tagFintype (b : A → Bit) (a : A) : Fintype (Tag T b a) := by
  classical
  unfold Tag
  infer_instance

abbrev LiftVertex (τ : G →g T) (b : A → Bit) := (u : V) × Tag T b (τ u)

noncomputable def liftGraph (τ : G →g T) (b : A → Bit) :
    SimpleGraph (LiftVertex T G τ b) where
  Adj u v := ∃ h : G.Adj u.1 v.1,
    u.2.1 ⟨τ v.1, τ.map_adj h⟩ = v.2.1 ⟨τ u.1, τ.map_adj h.symm⟩
  symm := ⟨by
    intro u v h
    rcases h with ⟨h, e⟩
    exact ⟨h.symm, e.symm⟩⟩
  loopless := ⟨by
    intro u h
    exact G.irrefl h.1⟩

end Lifts

noncomputable def starParity (t : ℕ) : TemplateVertex t → Bit :=
  fun a => if ∃ i : Fin t, i.val = 0 ∧ a = .inl i then 1 else 0

noncomputable def zeroLift {t : ℕ} (C : ChoiceSystem t) :=
  liftGraph (template t) (baseGraph C) (baseProjection C) (fun _ => 0)

noncomputable def starLift {t : ℕ} (C : ChoiceSystem t) :=
  liftGraph (template t) (baseGraph C) (baseProjection C) (starParity t)

inductive Convention | joint | separate
  deriving DecidableEq

def bagParameter (c : Convention) (k : ℕ) : ℕ :=
  match c with | .joint => k + 1 | .separate => k

def detectionRound : Convention → ℕ | .joint => 2 | .separate => 1

def orderFactor (t : ℕ) : ℕ :=
  t * 2 ^ (t - 2 + 3 * (t - 1).choose 2) + 12 * t.choose 3

abbrev AtomicType (k : ℕ) := Fin k → Fin k → Bool × Bool

def JointColor (k : ℕ) : ℕ → Type
  | 0 => AtomicType k
  | r + 1 => JointColor k r × Multiset (Fin k → JointColor k r)

def SeparateColor (k : ℕ) : ℕ → Type
  | 0 => AtomicType k
  | r + 1 => SeparateColor k r × (Fin k → Multiset (SeparateColor k r))

noncomputable def atomicType {V : Type} (G : SimpleGraph V) {k : ℕ}
    (x : Fin k → V) : AtomicType k := by
  classical
  exact fun i j => (decide (x i = x j), decide (G.Adj (x i) (x j)))

noncomputable def jointColor {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (r : ℕ) → (Fin k → V) → JointColor k r
  | 0, x => atomicType G x
  | r + 1, x => (jointColor G k r x,
      Finset.univ.val.map (fun y => fun i => jointColor G k r (Function.update x i y)))

noncomputable def separateColor {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (r : ℕ) → (Fin k → V) → SeparateColor k r
  | 0, x => atomicType G x
  | r + 1, x => (separateColor G k r x,
      fun i => Finset.univ.val.map (fun y => separateColor G k r (Function.update x i y)))

noncomputable def sameHistogram {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : Convention) (k r : ℕ) : Prop :=
  match c with
  | .joint => Finset.univ.val.map (jointColor G k r) =
      Finset.univ.val.map (jointColor H k r)
  | .separate => Finset.univ.val.map (separateColor G k r) =
      Finset.univ.val.map (separateColor H k r)

noncomputable def samePureHistogram {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : Convention) (k r : ℕ) : Prop :=
  match c with
  | .joint =>
      Finset.univ.val.map (fun x : Fin k → V => jointColor (G.sum H) k r (Sum.inl ∘ x)) =
      Finset.univ.val.map (fun x : Fin k → W => jointColor (G.sum H) k r (Sum.inr ∘ x))
  | .separate =>
      Finset.univ.val.map (fun x : Fin k → V => separateColor (G.sum H) k r (Sum.inl ∘ x)) =
      Finset.univ.val.map (fun x : Fin k → W => separateColor (G.sum H) k r (Sum.inr ∘ x))

noncomputable def WLEquivalent {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : Convention) (k : ℕ) : Prop :=
  ∀ r, sameHistogram G H c k r

noncomputable def PureWLEquivalent {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : Convention) (k : ℕ) : Prop :=
  ∀ r, samePureHistogram G H c k r

noncomputable def ParityReductionStatement : Prop :=
  ∀ (k : ℕ), 4 ≤ k → ∀ c : Convention, ∀ C : ChoiceSystem (bagParameter c k),
    let T := template (bagParameter c k)
    let G := baseGraph C
    let τ := baseProjection C
    let V₀ := LiftVertex T G τ (fun _ => 0)
    let V₁ := LiftVertex T G τ (starParity (bagParameter c k))
    Fintype.card V₀ = Fintype.card V₁ ∧
    (∀ A : ℕ, 1 ≤ A → C.SizeAtMost A → Fintype.card V₀ ≤ A * orderFactor (bagParameter c k)) ∧
    (WLEquivalent (zeroLift C) (starLift C) c k ↔ ¬ C.Successful) ∧
    (PureWLEquivalent (zeroLift C) (starLift C) c k ↔ ¬ C.Successful) ∧
    (C.Successful → ¬ sameHistogram (zeroLift C) (starLift C) c k (detectionRound c) ∧
      ¬ samePureHistogram (zeroLift C) (starLift C) c k (detectionRound c))

def parity_reduction_statement : Prop :=
  ParityReductionStatement

end ParityWL

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ParityWL.parity_reduction_statement

end Problem

/- Formalization scope, from lean/docs/133.md: The formalization gives the paper's parity-lift graph construction for every Weisfeiler–Leman dimension $k\ge4$, under both joint and separate conventions. From a finite choice system it constructs two equal-size uncolored graphs that are Weisfeiler–Leman equivalent exactly when the system has no successful compatible choice. The same equivalence holds for the pure variant. A successful choice is detected by the specified early round: round two in the joint convention and round one in the separate convention. The graph-size bound is linear in the choice-system size with a factor depending on $k$. The paper's conditional running-time exclusions are outside these selected construction statements. The formalization proves that deciding whether Weisfeiler–Leman refinement of a supplied dimension identifies a graph is EXPTIME-complete under polynomial-time many-one reductions. The input is a nonempty finite simple uncolored graph encoded by its adjacency matrix together with a positive binary-encoded dimension. Identification quantifies over every comparison graph, and the statement includes both the exponential-time upper bound and hardness. The formalization proves an unconditional deterministic time lower bound for deciding $k$-dimensional Weisfeiler–Leman equivalence. For every sufficiently large fixed $k$, every deciding algorithm in the stated multitape Turing-machine or sequential logarithmic-word RAM model requires at least $n^{ck}$ worst-case time for all sufficiently large graph orders $n$, for one absolute $c>0$. The bound covers both joint and separate replacement conventions and remains valid for explicit adjacency-matrix inputs restricted to simple connected uncolored graphs of diameter at most two. The formalization proves EXPTIME-completeness of deciding joint-update $k$-dimensional Weisfeiler–Leman equivalence when $k\ge2$ is part of the input in binary and the graphs are encoded by explicit adjacency matrices. It proves both the general result and the restriction to connected simple uncolored graphs of equal positive order and maximum degree at most three. Completeness uses polynomial-time many-one reductions. -/
