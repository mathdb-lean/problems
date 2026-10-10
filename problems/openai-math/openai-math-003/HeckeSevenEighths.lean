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

- problem_id: HeckeSevenEighths
- collection: openai-math
- question_id: openai-math:003
- source: openai-math
- source_locator: lean/ComparatorChallenges/HeckeSevenEighths.lean#OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that every Dirichlet L-function, including $`\zeta(s)`$, is zero-free in $`\Re s\gt 7/8`$, resolving the quasi-Riemann hypothesis. The same half-plane is zero-free for every finite-order Hecke L-function over $`\mathbb Q(\sqrt{-3})`$. A companion gives a different proof of the zero-free half-plane $`\Re s\gt 11/12`$. ([Lean](lean/docs/003.md)) We prove that all finite-order Hecke L-functions over $`\mathbb Q(\sqrt{-3})`$ and all Dirichlet L-functions are zero-free in the half-plane $`\Re s\gt 7/8`$, with the principal pole at s = 1 allowed. In particular, the Riemann zeta function is zero-free in this half-plane, proving the quasi-Riemann hypothesis. We prove the uniform exclusion of Landau–Siegel zeros. There is an absolute constant c &gt; 0 such that every real zero $`\beta\in(0,1)`$ of every primitive nonprincipal real Dirichlet L-function of conductor q ≥ 3 satisfies $`(1-\beta)\log q\ge c`$.
- notes: OpenAI math result family 003, The quasi-Riemann hypothesis -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/003.md
- track: solved
- answer_shape: proof
- context_lemmas: rapid_product_sub rapid_rescale shiftedPair_differentiableAt scaledEvenPair_f_continuous scaledEvenPair_g_continuous locallyIntegrableOn_sum
- source_theorem: OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.DirichletL.Hecke.Nonvanishing
- source_main_result: OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re
- source_papers: preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026/paper.pdf
- source_scope_note: lean/docs/003.md
- source_field: NumberTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators

namespace SevenEighths.ThetaProduct

theorem rapid_product_sub (f g : ℝ → ℂ) (a b : ℂ)
    (hf : ∀ r : ℝ, (fun x => f x - a) =O[atTop] (fun x : ℝ => x ^ r))
    (hg : ∀ r : ℝ, (fun x => g x - b) =O[atTop] (fun x : ℝ => x ^ r))
    (r : ℝ) :
    (fun x => f x * g x - a * b) =O[atTop] (fun x : ℝ => x ^ r) := by
  have hg0 : g =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    have hc : (fun _ : ℝ => b) =O[atTop] (fun x : ℝ => x ^ (0 : ℝ)) := by
      simpa using (isBigO_const_one ℝ b (atTop : Filter ℝ))
    have h := (hg 0).add hc
    simpa using h
  have h₁ := (hf r).mul hg0
  have h₂ := (hg r).const_mul_left a
  have hid : (fun x => f x * g x - a * b) =
      fun x => (f x - a) * g x + a * (g x - b) := by
    funext x
    ring
  rw [hid]
  have h₁' : (fun x => (f x - a) * g x) =O[atTop] (fun x : ℝ => x ^ r) := by
    simpa using h₁
  exact h₁'.add h₂

def product (P Q : WeakFEPair ℂ)
    (hPf : ContinuousOn P.f (Ioi 0)) (hPg : ContinuousOn P.g (Ioi 0))
    (hQf : ContinuousOn Q.f (Ioi 0)) (hQg : ContinuousOn Q.g (Ioi 0)) :
    WeakFEPair ℂ where
  f := fun x => P.f x * Q.f x
  g := fun x => P.g x * Q.g x
  k := P.k + Q.k
  ε := P.ε * Q.ε
  f₀ := P.f₀ * Q.f₀
  g₀ := P.g₀ * Q.g₀
  hf_int := (hPf.mul hQf).locallyIntegrableOn measurableSet_Ioi
  hg_int := (hPg.mul hQg).locallyIntegrableOn measurableSet_Ioi
  hk := add_pos P.hk Q.hk
  hε := mul_ne_zero P.hε Q.hε
  h_feq x hx := by
    rw [P.h_feq x hx, Q.h_feq x hx, Real.rpow_add hx]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  hf_top := rapid_product_sub P.f Q.f P.f₀ Q.f₀ P.hf_top Q.hf_top
  hg_top := rapid_product_sub P.g Q.g P.g₀ Q.g₀ P.hg_top Q.hg_top

theorem rapid_rescale (f : ℝ → ℂ) (a : ℂ)
    (hf : ∀ r : ℝ, (fun x => f x - a) =O[atTop] (fun x : ℝ => x ^ r))
    {u : ℝ} (hu : 0 < u) (r : ℝ) :
    (fun x => f (u * x) - a) =O[atTop] (fun x : ℝ => x ^ r) := by
  have ht : Tendsto (fun x : ℝ => u * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hu).2 tendsto_id
  have h := (hf r).comp_tendsto ht
  have heq : (fun x : ℝ => (u * x) ^ r) =ᶠ[atTop]
      (fun x : ℝ => u ^ r * x ^ r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.mul_rpow hu.le hx
  exact h.trans (heq.isBigO.trans ((isBigO_refl (fun x : ℝ => x ^ r) atTop).const_mul_left _))

def rescale (P : WeakFEPair ℂ)
    (hPf : ContinuousOn P.f (Ioi 0)) (hPg : ContinuousOn P.g (Ioi 0))
    (u : ℝ) (hu : 0 < u) : WeakFEPair ℂ where
  f := fun x => P.f (u * x)
  g := fun x => P.g (u⁻¹ * x)
  k := P.k
  ε := P.ε * (u ^ (-P.k) : ℝ)
  f₀ := P.f₀
  g₀ := P.g₀
  hf_int := (hPf.comp (by fun_prop) (fun x hx => mul_pos hu hx)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (hPg.comp (by fun_prop) (fun x hx => mul_pos (inv_pos.mpr hu) hx)).locallyIntegrableOn
    measurableSet_Ioi
  hk := P.hk
  hε := mul_ne_zero P.hε (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hu _).ne')
  h_feq x hx := by
    have heq : u * (1 / x) = 1 / (u⁻¹ * x) := by field_simp
    rw [heq, P.h_feq _ (mul_pos (inv_pos.mpr hu) hx),
      Real.mul_rpow (inv_pos.mpr hu).le hx.le, Real.inv_rpow hu.le,
      ← Real.rpow_neg hu.le]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  hf_top := rapid_rescale P.f P.f₀ P.hf_top hu
  hg_top := rapid_rescale P.g P.g₀ P.hg_top (inv_pos.mpr hu)

def shiftedPair (a b : UnitAddCircle) : WeakFEPair ℂ :=
  product (HurwitzZeta.hurwitzEvenFEPair a) (HurwitzZeta.hurwitzEvenFEPair b)
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel b))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel b))

@[simp] theorem shiftedPair_k (a b : UnitAddCircle) : (shiftedPair a b).k = 1 := by
  norm_num [shiftedPair, product, HurwitzZeta.hurwitzEvenFEPair]

@[simp] theorem shiftedPair_f (a b : UnitAddCircle) (t : ℝ) :
    (shiftedPair a b).f t =
      (HurwitzZeta.evenKernel a t : ℂ) * (HurwitzZeta.evenKernel b t : ℂ) := rfl

theorem shiftedPair_differentiableAt (a b : UnitAddCircle) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (shiftedPair a b).Λ s := by
  exact (shiftedPair a b).differentiableAt_Λ (Or.inl hs₀)
    (Or.inl (by simpa using hs₁))

def scaledEvenPair (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) : WeakFEPair ℂ :=
  rescale (HurwitzZeta.hurwitzEvenFEPair a)
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel a)) u hu

theorem scaledEvenPair_f_continuous (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) :
    ContinuousOn (scaledEvenPair a u hu).f (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (HurwitzZeta.continuousOn_evenKernel a)).comp (by fun_prop)
      (fun x hx => mul_pos hu hx)

theorem scaledEvenPair_g_continuous (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) :
    ContinuousOn (scaledEvenPair a u hu).g (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (HurwitzZeta.continuousOn_cosKernel a)).comp (by fun_prop)
      (fun x hx => mul_pos (inv_pos.mpr hu) hx)

def rectangularPair (a b : UnitAddCircle) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    WeakFEPair ℂ :=
  product (scaledEvenPair a u hu) (scaledEvenPair b v hv)
    (scaledEvenPair_f_continuous a u hu) (scaledEvenPair_g_continuous a u hu)
    (scaledEvenPair_f_continuous b v hv) (scaledEvenPair_g_continuous b v hv)

@[simp] theorem rectangularPair_k (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) : (rectangularPair a b u v hu hv).k = 1 := by
  norm_num [rectangularPair, scaledEvenPair, rescale, product, HurwitzZeta.hurwitzEvenFEPair]

end SevenEighths.ThetaProduct

namespace SevenEighths.EisensteinTheta
open ThetaProduct

def xShift (a b L : ℝ) (e : Fin 2) : ℝ := (2 * a - b - L * e) / (2 * L)
def yShift (b L : ℝ) (e : Fin 2) : ℝ := (b + L * e) / (2 * L)

def parityPair (a b L : ℝ) (hL : 0 < L) (e : Fin 2) : WeakFEPair ℂ :=
  rectangularPair (xShift a b L e) (yShift b L e) (L ^ 2) (3 * L ^ 2)
    (sq_pos_of_pos hL) (mul_pos (by norm_num) (sq_pos_of_pos hL))

end SevenEighths.EisensteinTheta

namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem locallyIntegrableOn_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) (Ioi 0)) :
    LocallyIntegrableOn (∑ i ∈ s, f i) (Ioi 0) := by
  exact Finset.sum_induction f (fun g => LocallyIntegrableOn g (Ioi 0))
    (fun _ _ => LocallyIntegrableOn.add) (locallyIntegrableOn_const 0) hf

def finitePair {ι : Type*} [Fintype ι] (P : ι → WeakFEPair ℂ)
    (hk : ∀ i, (P i).k = 1) (w : ι → ℂ) : WeakFEPair ℂ where
  f := ∑ i, w i • (P i).f
  g := ∑ i, (w i * (P i).ε) • (P i).g
  k := 1
  ε := 1
  f₀ := ∑ i, w i * (P i).f₀
  g₀ := ∑ i, w i * (P i).ε * (P i).g₀
  hf_int := locallyIntegrableOn_sum Finset.univ _
    (fun i _ => (P i).hf_int.smul (w i))
  hg_int := locallyIntegrableOn_sum Finset.univ _
    (fun i _ => (P i).hg_int.smul (w i * (P i).ε))
  hk := by norm_num
  hε := one_ne_zero
  h_feq x hx := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(P i).h_feq x hx, hk i]
    simp only [smul_eq_mul]
    ring
  hf_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hf_top r).const_mul_left (w i))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h
  hg_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hg_top r).const_mul_left (w i * (P i).ε))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h

def pair {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : WeakFEPair ℂ :=
  finitePair (fun p : (Fin N × Fin N) × Fin 2 =>
    parityPair p.1.1 p.1.2 N (Nat.cast_pos.mpr (NeZero.pos N)) p.2)
    (fun _ => ThetaProduct.rectangularPair_k ..) (fun p => w p.1)

def completed {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : ℂ → ℂ := (pair w).Λ

def latticeL {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * completed w s

end SevenEighths.HeckeTheta

namespace SevenEighths.HeckeFamily

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

def omega : O := (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def coordinateElement (x y : ℤ) : O := (x : O) + (y : O) * omega

structure Character where
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  residue : MulChar (O ⧸ modulus) ℂ
  unit_trivial : ∀ u : Oˣ, residue (Ideal.Quotient.mk modulus (u : O)) = 1
  period : ℕ
  period_pos : 0 < period
  period_mem : (period : O) ∈ modulus

instance (χ : Character) : NeZero χ.period := ⟨Nat.ne_of_gt χ.period_pos⟩

def elementCoeff (χ : Character) (z : O) : ℂ := χ.residue (Ideal.Quotient.mk χ.modulus z)

def coefficients (χ : Character) (a : Fin χ.period × Fin χ.period) : ℂ :=
  elementCoeff χ (coordinateElement a.1 a.2)

def continuedLattice (χ : Character) : ℂ → ℂ := HeckeTheta.latticeL (coefficients χ)

def LFunction (χ : Character) (s : ℂ) : ℂ := continuedLattice χ s / 6

def LFunction_ne_zero_of_seven_eighths_lt_re_statement : Prop :=
  ∀ (χ : Character) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ.residue = 1 ∧ s = 1)),
    LFunction χ s ≠ 0

end SevenEighths.HeckeFamily

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re_statement

end Problem

/- Formalization scope, from lean/docs/003.md: The quasi-Riemann hypothesis asks for a fixed zero-free half-plane $\Re s>\theta$ with $\theta<1$. The formalization gives $\theta=7/8$ for the Riemann zeta function and every Dirichlet $L$-function, uniformly over all positive moduli and all characters. It also establishes the same bound for finite-order Hecke $L$-functions over $\mathbb Q(\sqrt{-3})$. The principal-character poles at $s=1$ are excluded in the Dirichlet and Hecke statements. The paper's later applications are not included. The formalized result gives a uniform logarithmic exclusion region for Landau–Siegel zeros. There is one constant $c>0$ such that every primitive nonprincipal real Dirichlet character of conductor $q\ge3$ and every real zero $0<\beta<1$ of its $L$-function satisfy $1-\beta\ge c/\log q$. Both character parities are included. No explicit value of $c$ is given. This excludes real zeros in $1-c/\log q<\beta<1$, but does not rule out real zeros elsewhere in $(0,1)$. -/
