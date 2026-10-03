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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E5_prove
- collection: erdos
- question_id: erdos:5
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/5.lean#erdos_5
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $C\geq 0$. Is there an infinite sequence of $n_i$ such that $$\lim_{i\to \infty}\frac{p_{n_i+1}-p_{n_i}}{\log n_i}=C?$$ We formalise "an infinite sequence of $n_i$" as a strictly monotone sequence of indices `n : ℕ → ℕ`. Note that the numerator is the gap between the two *consecutive* primes $p_{n_i}$ and $p_{n_i+1}$, which is `primeGap (n i)`, and not the gap between the primes indexed by two consecutive members of the sequence.
- notes: Erdos Problem 5 -- https://www.erdosproblems.com/5
- track: open
- answer_shape: prove
- pair_id: E5
- pair_role: prove
- source_stem: 5
- mathdb_ref: erdos:5
- source_namespace: Erdos5
- source_theorem: erdos_5
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: mem_limitPointSet_iff normalizedGap_nonneg limitPointSet_subset_Ici isClosed_limitPointSet dense_iff_limit_point_set
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter MeasureTheory Real Set
open scoped Topology

namespace Problem

/--
The normalised prime gap $\frac{p_{n+1}-p_n}{\log n}$, where $p_n$ denotes the $n$-th prime.
-/
noncomputable def normalizedGap (n : ℕ) : ℝ := primeGap n / log n

/--
The set $S$ of limit points of $\frac{p_{n+1}-p_n}{\log n}$.

Only the *finite* limit points are collected here; that $\infty$ is also a limit point is
Westzynthius' theorem, recorded separately as `erdos_5.variants.westzynthius`.

Erdős' question, as well as [HiMa88] and [Pi16], normalises the prime gaps by $\log n$, whereas
[GPY09], [BFM16] and [Me20] normalise by $\log p_n$. Since $\log p_n/\log n \to 1$ the two
normalisations have the same limit points, so all the results below are stated for the
normalisation used here.
-/
def limitPointSet : Set ℝ := {x : ℝ | MapClusterPt x atTop normalizedGap}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
Membership in `limitPointSet` is exactly the existence of an infinite sequence of indices
along which the normalised prime gaps converge, as in the statement of `erdos_5`.
-/
@[category test, AMS 11]
theorem mem_limitPointSet_iff (x : ℝ) : x ∈ limitPointSet ↔
    ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => normalizedGap (n i)) atTop (𝓝 x) :=
  ⟨fun hx => hx.tendsto_subseq, fun ⟨_n, hn, h⟩ => h.mapClusterPt.of_comp hn.tendsto_atTop⟩

/-- The normalised prime gaps are nonnegative. -/
@[category test, AMS 11]
theorem normalizedGap_nonneg (n : ℕ) : 0 ≤ normalizedGap n :=
  div_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)

/-- Every limit point of the normalised prime gaps is nonnegative. -/
@[category test, AMS 11]
theorem limitPointSet_subset_Ici : limitPointSet ⊆ Ici 0 := by
  intro x hx
  obtain ⟨n, -, h⟩ := (mem_limitPointSet_iff x).1 hx
  exact ge_of_tendsto' h fun i => normalizedGap_nonneg (n i)

/--
The set $S$ of limit points is closed, as Weisenberg notes in the acknowledgements to
[erdosproblems.com/5](https://www.erdosproblems.com/5); consequently `erdos_5.variants.dense`
and `erdos_5.variants.limit_point_set` ask the same question.
-/
@[category test, AMS 11]
theorem isClosed_limitPointSet : IsClosed limitPointSet := isClosed_setOfPred_clusterPt

/--
Weisenberg's remark, as reported on [erdosproblems.com/5](https://www.erdosproblems.com/5):
since $S$ is closed, asking that $S$ be everywhere dense in $[0,\infty)$ is the same as asking
that $S=[0,\infty)$, so `erdos_5.variants.dense` and `erdos_5.variants.limit_point_set` pose the
same question.
-/
@[category test, AMS 11]
theorem dense_iff_limit_point_set :
    Ici (0 : ℝ) ⊆ closure limitPointSet ↔ limitPointSet = Ici 0 := by
  rw [isClosed_limitPointSet.closure_eq]
  exact ⟨fun h => limitPointSet_subset_Ici.antisymm h, fun h => h.ge⟩

-- See also Erdős Problem 234, which concerns the density of the integers `n` with
-- `(p (n + 1) - p n) / log n < c`.

abbrev Target : Prop :=
    ∀ C : ℝ, 0 ≤ C →
        ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => normalizedGap (n i)) atTop (𝓝 C)

end Problem
