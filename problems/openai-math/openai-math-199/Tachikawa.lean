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

- problem_id: Tachikawa
- collection: openai-math
- question_id: openai-math:199
- source: openai-math
- source_locator: lean/ComparatorChallenges/Tachikawa.lean#OAI.Tachikawa.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs finite-dimensional algebras over a characteristic-two rational-function field that disprove the Auslander–Reiten and Gorenstein-projective conjectures, and Tachikawa's second conjecture. An associated endomorphism algebra also disproves the classical, generalized and strong Nakayama conjectures, the Auslander–Gorenstein conjecture, and the Wakamatsu tilting conjecture. The counterexamples persist under every extension of the base field. ([Lean](lean/docs/199.md)) We disprove the Auslander–Reiten conjecture for Artin algebras. We construct a finite-dimensional algebra Λ over $`k=\mathbb F_2(q,H_1,H_2)`$ and a finite-dimensional nonprojective left module Z such that $`\mathop{\mathrm{Ext}}\nolimits ^i_\Lambda(Z,Z)=\mathop{\mathrm{Ext}}\nolimits ^i_\Lambda(Z,\Lambda)=0`$ for every i &gt; 0. The module is Gorenstein-projective, so the same example also disproves the Gorenstein-projective conjecture. Both counterexamples persist after every extension of k. We disprove Tachikawa's second conjecture by constructing a finite-dimensional symmetric algebra over $`k=\mathbb F_2(q,H_1,H_2)`$ with a finite-dimensional nonprojective module whose self-extension groups vanish in every positive degree. The associated endomorphism algebra also gives counterexamples to the classical, generalized, and strong Nakayama conjectures, the Auslander–Gorenstein conjecture, and the Wakamatsu tilting conjecture. These conclusions persist after every extension of k.
- notes: OpenAI math result family 199, Counterexamples to Auslander–Reiten, Tachikawa and related homological conjectures -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/199.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Tachikawa.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.RingTheory.Tachikawa.Counterexample
- source_main_result: OAI.Tachikawa.main_theorem
- source_papers: preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/199.md
- source_field: RingTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Tachikawa

noncomputable section

abbrev k := FractionRing (MvPolynomial (Fin 3) (ZMod 2))

def SymmetricOver (K A : Type) [Field K] [Ring A] [Algebra K A] : Prop :=
  ∃ e : A ≃ₗ[K] Module.Dual K A,
    (∀ a b c : A, e (a * b) c = e b (c * a)) ∧
    (∀ a b c : A, e (a * b) c = e a (b * c))

def Counterexample : Prop :=
  ∃ (A : Type) (rA : Ring A),
    letI := rA
    ∃ (aA : Algebra k A),
      letI := aA
      Module.Finite k A ∧ SymmetricOver k A ∧
      ∃ (M : Type) (gM : AddCommGroup M),
        letI := gM
        ∃ (mA : Module A M) (mk : Module k M),
          letI := mA
          letI := mk
          IsScalarTower k A M ∧ Module.Finite k M ∧
          ¬ Module.Projective A M ∧
          ∀ n : ℕ, 0 < n →
            Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A M) n)

def main_theorem_statement : Prop :=
  Counterexample

end

end Tachikawa

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Tachikawa.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/199.md: The Auslander–Reiten conjecture predicts that a finitely generated module $M$ over an Artin algebra $A$ is projective if $\mathrm{Ext}^i_A(M,M\oplus A)=0$ for every $i>0$. The formalized counterexample is a finite-dimensional algebra over $k=\mathbb F_2(q,H_1,H_2)$ and a finite-dimensional nonprojective Gorenstein-projective module with this vanishing. It also establishes $A/\mathrm{rad}\,A\cong k^8$, $(\mathrm{rad}\,A)^4\ne0$, and preservation of the listed properties after every field extension. The Tachikawa companion is separate. Tachikawa's second conjecture predicts that a finite-dimensional module over a finite-dimensional self-injective algebra is projective if all its positive-degree self-Ext groups vanish. The formalized counterexample gives a finite-dimensional symmetric algebra over $\mathbb F_2(q,H_1,H_2)$ and a finite-dimensional nonprojective module $M$ with $\mathrm{Ext}^i(M,M)=0$ for every $i>0$. Symmetric algebras are self-injective, so this contradicts the conjecture. The later field-extension, endomorphism-algebra, and related homological consequences are not included. -/
