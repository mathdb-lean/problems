/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: NGoodmanConjecture_goodman_conjecture
- collection: wikipedia
- question_id: wikipedia:GoodmanConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/GoodmanConjecture.lean#goodman_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Goodman's conjecture.** For every $p$-valent normalised function $f$ on the unit disk and every $n > p$, the $n$-th coefficient is bounded by the Goodman bound: $$|b_n| \le \sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|.$$
- notes: Wikipedia: GoodmanConjecture -- https://en.wikipedia.org/wiki/Goodman%27s_conjecture
- track: open
- answer_shape: proof
- source_stem: GoodmanConjecture
- source_namespace: GoodmanConjecture
- source_theorem: goodman_conjecture
- source_category: research open
- source_ams: 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: isPValent_id_one goodmanBound_one
- generator: adapters/formal_conjectures/adapter.py
-/

open Complex Set

namespace Problem

/-- A function `f : ℂ → ℂ` is **$p$-valent** on the open unit disk $\mathbb{D} = \{z : |z| < 1\}$
if it is analytic there, attains every value at most $p$ times, and attains some value exactly
$p$ times. Here $p \ge 1$.
Values are counted at distinct points. For a non-constant analytic function this agrees with
counting with multiplicity: near a point where $f - w$ has a zero of order $m$, every value close
to $w$ is attained at $m$ distinct points, so the maximal number of distinct preimages equals the
maximal number of preimages counted with multiplicity. -/
structure IsPValent (f : ℂ → ℂ) (p : ℕ) : Prop where
  one_le_p   : 1 ≤ p
  analyticOn : AnalyticOn ℂ f (Metric.ball 0 1)
  /-- Every value $w$ is attained at most $p$ times on the disk. -/
  atMost     : ∀ w : ℂ, {z ∈ Metric.ball 0 1 | f z = w}.encard ≤ p
  /-- Some value $w$ is attained exactly $p$ times on the disk. -/
  exactly    : ∃ w : ℂ, {z ∈ Metric.ball 0 1 | f z = w}.encard = p

/-- The $n$-th Taylor coefficient of $f$ at $0$, i.e. $b_n = f^{(n)}(0) / n!$. -/
noncomputable def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

/-- Goodman's normalisation $f(z) = \sum_{n \ge 1} b_n z^n$, i.e. $f(0) = 0$. -/
structure IsNormalized (f : ℂ → ℂ) : Prop where
  map_zero   : f 0 = 0

/-- The Goodman bound
$$\sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|,$$
the conjectured upper bound for $|b_n|$. -/
noncomputable def goodmanBound (f : ℂ → ℂ) (p n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 p,
    (2 * k * (n + p).factorial : ℝ) /
      ((p - k).factorial * (p + k).factorial * (n - p - 1).factorial * ((n : ℝ) ^ 2 - k ^ 2)) *
      ‖coeff f k‖

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The identity is $1$-valent (univalent) on the unit disk. -/
@[category test, AMS 30]
theorem isPValent_id_one : IsPValent id 1 where
  one_le_p := le_rfl
  analyticOn := analyticOnNhd_id.analyticOn
  atMost := fun w => by
    calc {z ∈ Metric.ball (0 : ℂ) 1 | id z = w}.encard ≤ ({w} : Set ℂ).encard :=
          Set.encard_le_encard (fun z hz => by simpa using hz.2)
      _ = 1 := by simp
  exactly := ⟨0, by
    have : {z ∈ Metric.ball (0 : ℂ) 1 | id z = 0} = {0} := by
      ext z
      constructor
      · rintro ⟨-, h⟩; simpa using h
      · rintro rfl; simp
    rw [this]; simp⟩

/--
Sanity check: in the univalent case $p = 1$, the Goodman bound reduces to the classical
Bieberbach-type bound $|b_n| \le n\,|b_1|$. Concretely the single $k = 1$ summand is
$$\frac{2 (n+1)!}{0!\,2!\,(n-2)!\,(n^2-1)} = \frac{(n+1)!}{(n-2)!\,(n^2-1)} = n,$$
so the bound equals $n\,|b_1|$.
-/
@[category test, AMS 30]
theorem goodmanBound_one (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n) :
    goodmanBound f 1 n = n * ‖coeff f 1‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [goodmanBound, Finset.Icc_self, Finset.sum_singleton]
  congr 1
  have e3 : (m + 2 - 1 - 1 : ℕ) = m := by omega
  have e4 : (m + 2 + 1 : ℕ) = m + 3 := by omega
  rw [e3, e4]
  have hfact : ((m + 3).factorial : ℝ) = (m + 3) * (m + 2) * (m + 1) * (m.factorial : ℝ) := by
    have h1 : (m + 3).factorial = (m + 3) * (m + 2).factorial := rfl
    have h2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := rfl
    have h3 : (m + 1).factorial = (m + 1) * m.factorial := rfl
    rw [h1, h2, h3]; push_cast; ring
  rw [hfact]
  have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hm3 : ((m : ℝ) + 3) ≠ 0 := by positivity
  have hsq : ((m : ℝ) + 2) ^ 2 - (1 : ℝ) ^ 2 = ((m : ℝ) + 1) * ((m : ℝ) + 3) := by ring
  push_cast
  rw [hsq]
  field_simp
  ring

abbrev Target : Prop :=
    ∀ (f : ℂ → ℂ) (p n : ℕ) (hf : IsPValent f p)
        (hf' : IsNormalized f) (hn : p < n),
      ‖coeff f n‖ ≤ goodmanBound f p n

end Problem
