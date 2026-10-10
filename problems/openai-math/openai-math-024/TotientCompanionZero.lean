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

- problem_id: TotientCompanionZero
- collection: openai-math
- question_id: openai-math:024
- source: openai-math
- source_locator: lean/ComparatorChallenges/TotientCompanionZero.lean#OAI.TotientAsymptotic.companion_zero_case
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives an asymptotic equivalent for the number $`V(x)`$ of distinct totient values up to x, with a positive bounded phase-dependent factor determined by convergent arithmetic approximations. In particular, $`V(cx)/V(x)\to c`$ for every fixed c &gt; 0, answering Erdős and Hall’s scaling question. ([Lean](lean/docs/024.md)) Let $`V(x)`$ count the distinct values of Euler's totient function up to x. We give an explicit asymptotic equivalent for $`V(x)`$. Its coefficient is a uniform limit of functions defined from finite arithmetic data. We also prove that $`V(cx)/V(x)\to c`$ as $`x\to\infty`$ for every fixed c &gt; 0, answering a question of Erdős and Hall.
- notes: OpenAI math result family 024, An asymptotic formula for the number of totients -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/024.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.TotientAsymptotic.companion_zero_case
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.TotientAsymptotic.Main
- source_papers: preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf
- source_scope_note: lean/docs/024.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! The no-seed alternative of the weighted totient companion theorem. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def IsTotient (v : ℕ) : Prop := ∃ n : ℕ, 0 < n ∧ n.totient = v

def ell (v : ℕ) : ℕ := by
  classical
  exact if h : IsTotient v then Nat.find h else 0

def a (j : ℕ) : ℝ := (j + 1 : ℝ) * Real.log (j + 1) - j * Real.log j - 1

def RenewalRootSet : Set ℝ :=
  {z | 0 < z ∧ z < 1 ∧ (∑' j : ℕ, a (j+1) * z^(j+1)) = 1}

def rho : ℝ := sInf RenewalRootSet

def lam : ℝ := Real.log (1 / rho)

def gamma : ℝ := (∑' j : ℕ, (j+1 : ℝ) * a (j+1) * rho^(j+1))⁻¹

def P (H : ℕ) : ℕ := ⌊Real.log (Real.log (H : ℝ))⌋₊
def alpha (s : ℝ) : ℝ := lam * Real.exp (lam * s)

def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)

structure TailDatum (H : ℕ) where
  Q : Fin H → ℕ
  cofactor : ℕ

def tailPrime {H : ℕ} (η : TailDatum H) (h : ℕ) : ℕ :=
  if hH : h < H then η.Q ⟨h, hH⟩ else 1

def tailLog {H : ℕ} (η : TailDatum H) (h : ℕ) : ℝ :=
  Real.log (Real.log (tailPrime η h : ℝ))

def IsWitness (H : ℕ) (s : ℝ) (η : TailDatum H) : Prop :=
  (∀ h : Fin H, h.val < P H → η.Q h = 1) ∧
  0 < η.cofactor ∧
  (∀ h ∈ Finset.Ico (P H) H, (tailPrime η h).Prime ∧
    (9 / 10 : ℝ) * alpha s * h * (rho^h)⁻¹ ≤ tailLog η h ∧
    tailLog η h ≤ (11 / 10 : ℝ) * alpha s * h * (rho^h)⁻¹ ∧
    (∑ l ∈ Finset.Ico (P H) h, a (h-l) * tailLog η l) ≤
      (1 + (1 / 10000 : ℝ) * Real.exp (-(h : ℝ) / 40)) * tailLog η h) ∧
  largestPrimeFactor η.cofactor ≤ tailPrime η (P H) ∧
  Real.log (η.cofactor : ℝ) ≤
    Real.exp (2 * alpha s * (P H : ℝ) * (rho^(P H))⁻¹)

def w {H : ℕ} (η : TailDatum H) : ℕ :=
  η.cofactor * ∏ h ∈ Finset.Ico (P H) H, tailPrime η h

def witnesses (H : ℕ) (s : ℝ) (d : ℕ) : Set (TailDatum H) :=
  {η | IsWitness H s η ∧ (w η).totient = d}

def D {H : ℕ} (h : ℕ) (η : TailDatum H) : ℝ :=
  ∑ l ∈ Finset.Ico (P H) H, a (h-l) * tailLog η l

def maxD {H : ℕ} (h : ℕ) (T : Finset (TailDatum H)) : ℝ := by
  classical
  exact if ht : T.Nonempty then T.sup' ht (D h) else 0

def AH (H : ℕ) (f : ℝ → ℝ) (s : ℝ) : ℝ := by
  classical
  exact rho^(H*(H-1)/2) * (gamma / alpha s)^H *
    ∑ᶠ d : ℕ,
      if IsTotient d then
        f ((ell d : ℝ) / d) / d *
          ∑ᶠ T : Finset (TailDatum H),
            if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
              (-1 : ℝ)^(T.card-1) *
               Real.exp (-(gamma / alpha s) *
                 ∑' n : ℕ, rho^(H+n) * maxD (H+n) T)
            else 0
      else 0

def A (f : ℝ → ℝ) (s : ℝ) : ℝ := limUnder atTop (fun H : ℕ => AH H f s)

def N (k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact (((Finset.Icc 1 ⌊x⌋₊).filter fun v =>
    IsTotient v ∧ (k : ℝ) * x < ell v ∧ (ell v : ℝ) ≤ (k+1 : ℝ) * x).card : ℝ)

def fk (k : ℕ) (r : ℝ) : ℝ := min 1 ((k+1 : ℝ) / r) - min 1 ((k : ℝ) / r)

/-- Without a totient value whose least preimage exceeds its prescribed multiple,
both the weighted count and its limiting coefficient vanish. -/
def companion_zero_case_statement : Prop :=
  ∀ (k : ℕ) (_hk : 0 < k) (hno : ¬ ∃ d : ℕ, IsTotient d ∧ k*d < ell d),
    (∀ x : ℝ, 0 < x → N k x = 0) ∧
    (∀ s ∈ Set.Ico (0 : ℝ) 1, A (fk k) s = 0)

end TotientAsymptotic
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.TotientAsymptotic.companion_zero_case_statement

end Problem

/- Formalization scope, from lean/docs/024.md: Let $V(x)$ count the distinct values of Euler's totient function up to $x$. The formalization constructs the paper's explicit positive main term from finite arithmetic approximants and proves that their ratio tends to one. In particular, $V(cx)/V(x)\to c$ for every fixed $c>0$, answering the Erdős–Hall regular-variation question. The formalization also gives asymptotics for totients $v\le x$ whose least preimage $\ell(v)=\min\{n\ge1:\varphi(n)=v\}$ lies between $kx$ and $(k+1)x$. The associated coefficient is positive under the stated existence condition; when no totient $d$ satisfies $kd<\ell(d)$, the count and coefficient are identically zero. The cases $k=1,2$ have positive coefficients. -/
