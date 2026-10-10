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

- problem_id: TypeSystemNormalization
- collection: openai-math
- question_id: openai-math:245
- source: openai-math
- source_locator: lean/ComparatorChallenges/TypeSystemNormalization.lean#OAI.PureTypeSystem.weak_implies_strong
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that weak normalization implies strong normalization for every pure type system: if every legal expression in every valid context has a β-normal form, every β-reduction sequence terminates. This resolves the β-Barendregt–Geuvers–Klop conjecture, including nonfunctional rules and open contexts. ([Lean](lean/docs/245.md)) We prove that every weakly β-normalizing pure type system is strongly β-normalizing. Both properties quantify over all legal expressions in all valid contexts, and reduction acts inside type annotations. No functionality hypothesis is required. This resolves the β-Barendregt–Geuvers–Klop conjecture.
- notes: OpenAI math result family 245, Weak normalization implies strong normalization in pure type systems -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/245.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PureTypeSystem.weak_implies_strong
- source_theorem_count: 1
- source_solution_module: OAI.Computability.TypeSystem.Normalization
- source_papers: preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf
- source_scope_note: lean/docs/245.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
Full annotated PTS syntax, modulo alpha-renaming via de Bruijn indices.
Contexts are stored newest-first, each declaration in its prefix context.
No functionality assumptions on axioms or product rules.
-/

namespace PureTypeSystem

universe u

inductive Expr (Sorts : Type u) : Type u
  | var : Nat → Expr Sorts
  | sort : Sorts → Expr Sorts
  | app : Expr Sorts → Expr Sorts → Expr Sorts
  | lam : Expr Sorts → Expr Sorts → Expr Sorts
  | pi : Expr Sorts → Expr Sorts → Expr Sorts
  deriving DecidableEq

namespace Expr

variable {S : Type u}

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def rename (ρ : Nat → Nat) : Expr S → Expr S
  | var n => var (ρ n)
  | sort s => sort s
  | app f a => app (rename ρ f) (rename ρ a)
  | lam A b => lam (rename ρ A) (rename (liftRen ρ) b)
  | pi A B => pi (rename ρ A) (rename (liftRen ρ) B)

def liftSub (σ : Nat → Expr S) : Nat → Expr S
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

def subst (σ : Nat → Expr S) : Expr S → Expr S
  | var n => σ n
  | sort s => sort s
  | app f a => app (subst σ f) (subst σ a)
  | lam A b => lam (subst σ A) (subst (liftSub σ) b)
  | pi A B => pi (subst σ A) (subst (liftSub σ) B)

def single (a : Expr S) : Nat → Expr S
  | 0 => a
  | n + 1 => var n

def instantiate (b a : Expr S) : Expr S := subst (single a) b

end Expr

structure Specification (S : Type u) where
  axioms : S → S → Prop
  rule : S → S → S → Prop

inductive Beta {S : Type u} : Expr S → Expr S → Prop
  | head (A b a) : Beta (.app (.lam A b) a) (b.instantiate a)
  | app_left {f f' a} : Beta f f' → Beta (.app f a) (.app f' a)
  | app_right {f a a'} : Beta a a' → Beta (.app f a) (.app f a')
  | lam_domain {A A' b} : Beta A A' → Beta (.lam A b) (.lam A' b)
  | lam_body {A b b'} : Beta b b' → Beta (.lam A b) (.lam A b')
  | pi_domain {A A' B} : Beta A A' → Beta (.pi A B) (.pi A' B)
  | pi_body {A B B'} : Beta B B' → Beta (.pi A B) (.pi A B')

def Converts {S : Type u} : Expr S → Expr S → Prop := Relation.EqvGen Beta

def Normal {S : Type u} (M : Expr S) : Prop := ∀ N, ¬ Beta M N

def WeaklyNormalizing {S : Type u} (M : Expr S) : Prop :=
  ∃ N, Relation.ReflTransGen Beta M N ∧ Normal N

/-- Accessibility for the converse of reduction: strong normalization,
including reductions in all type annotations. -/
def StronglyNormalizing {S : Type u} (M : Expr S) : Prop :=
  Acc (fun N M : Expr S => Beta M N) M

inductive HasType {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasType P [] (.sort s) (.sort t)
  | var {Γ A s} : HasType P Γ A (.sort s) →
      HasType P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken {Γ M B A s} : HasType P Γ M B → HasType P Γ A (.sort s) →
      HasType P (A :: Γ) (M.rename Nat.succ) (B.rename Nat.succ)
  | product {Γ A B s₁ s₂ s₃} : HasType P Γ A (.sort s₁) →
      HasType P (A :: Γ) B (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasType P Γ (.pi A B) (.sort s₃)
  | abstraction {Γ A b B s} : HasType P (A :: Γ) b B →
      HasType P Γ (.pi A B) (.sort s) →
      HasType P Γ (.lam A b) (.pi A B)
  | application {Γ f a A B} : HasType P Γ f (.pi A B) →
      HasType P Γ a A → HasType P Γ (.app f a) (B.instantiate a)
  | conversion {Γ M A B s} : HasType P Γ M A → HasType P Γ B (.sort s) →
      Converts A B → HasType P Γ M B

inductive ValidContext {S : Type u} (P : Specification S) : List (Expr S) → Prop
  | nil : ValidContext P []
  | cons {Γ A s} : ValidContext P Γ → HasType P Γ A (.sort s) →
      ValidContext P (A :: Γ)

def Legal {S : Type u} (P : Specification S) (Γ : List (Expr S)) (M : Expr S) : Prop :=
  ∃ A, HasType P Γ M A ∨ HasType P Γ A M

def SystemWeaklyNormalizing {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ, ValidContext P Γ → ∀ M, Legal P Γ M → WeaklyNormalizing M

def SystemStronglyNormalizing {S : Type u} (P : Specification S) : Prop :=
  ∀ Γ, ValidContext P Γ → ∀ M, Legal P Γ M → StronglyNormalizing M

/-- System-wide weak normalization implies strong normalization for every PTS,
including arbitrary sort types, nonfunctional rules and annotated terms. -/
def weak_implies_strong_statement : Prop :=
  ∀ {S : Type u} (P : Specification S) (h : SystemWeaklyNormalizing P),
    SystemStronglyNormalizing P

end PureTypeSystem

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.PureTypeSystem.weak_implies_strong_statement.{u}

end Problem

/- Formalization scope, from lean/docs/245.md: The formalization proves the $\beta$-Barendregt–Geuvers–Klop conjecture for pure type systems: if every legal expression in every valid context has some terminating $\beta$-reduction sequence, then every $\beta$-reduction sequence from every such expression terminates. Reduction is allowed inside type annotations, and the specification may have arbitrary sorts and nonfunctional axioms or rules. -/
