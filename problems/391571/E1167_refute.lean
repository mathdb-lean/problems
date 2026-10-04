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

- problem_id: E1167_refute
- collection: erdos
- question_id: erdos:1167
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1167.lean#erdos_1167
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 1167.** Let $r \geq 2$ be finite, $\gamma \geq 2$, and $\lambda$ be an infinite cardinal. Let $\kappa_\alpha > r$ be cardinals for all $\alpha < \gamma$. Is it true that $$2^\lambda \to (\kappa_\alpha + 1)_{\alpha < \gamma}^{r+1}$$ implies $$\lambda \to (\kappa_\alpha)_{\alpha < \gamma}^r?$$ Here $+$ means cardinal addition, so that $\kappa_\alpha + 1 = \kappa_\alpha$ if $\kappa_\alpha$ is infinite. A problem of Erdős, Hajnal, and Rado.
- notes: Erdos Problem 1167 -- https://www.erdosproblems.com/1167
- track: open
- answer_shape: refute
- pair_id: E1167
- pair_role: refute
- source_stem: 1167
- mathdb_ref: erdos:1167
- source_namespace: Erdos1167
- source_theorem: erdos_1167
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: cardinalPartitionRel_one
- generator: adapters/formal_conjectures/adapter.py
-/

open Cardinal Ordinal Combinatorics

namespace Problem

universe u

namespace erdos_1167.variants

end erdos_1167.variants

/- ## Counterexample for the unrestricted statement

The partition relation $\mu \to (\nu)^r_1$ with a single color ($\gamma = 1$) degenerates to the
cardinality comparison $\nu \leq \mu$. Using this, we show the unrestricted version of Erdős
Problem 1167 (without $\gamma \geq 2$) is false.
-/

/-- A canonical element of the type `(1 : Ordinal).ToType`. -/
noncomputable def i0 : (1 : Ordinal.{u}).ToType := default

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
The partition relation $\mu \to (\nu)^r_1$ with a single color is equivalent to $\nu \le \mu$.
-/
@[category API, AMS 5]
lemma cardinalPartitionRel_one (μ : Cardinal.{u}) (r : ℕ)
    (ν : (1 : Ordinal.{u}).ToType → Cardinal.{u}) :
    cardinalPartitionRel μ r 1 ν ↔ μ ≥ ν i0 := by
  dsimp [cardinalPartitionRel]
  constructor
  · intro h
    have hA : #(μ.out) = μ := Cardinal.mk_out μ
    rcases h μ.out hA (fun _ => i0) with ⟨i, H, hH, _⟩
    have hi : i = i0 := Subsingleton.elim i i0
    subst hi
    have hle : #H ≤ #(μ.out) := Cardinal.mk_set_le H
    rw [hH, hA] at hle
    exact hle
  · intro h A hA col
    have hle : ν i0 ≤ #A := by rwa [hA]
    rcases Cardinal.le_mk_iff_exists_set.mp hle with ⟨H, hH⟩
    use i0, H, hH
    intro s hs hsH
    exact Subsingleton.elim _ _

abbrev Target : Prop :=
    ¬ (
      ∀ (r : ℕ), 2 ≤ r →
          ∀ (lam : Cardinal.{u}), ℵ₀ ≤ lam →
          ∀ (γ : Ordinal.{u}), 2 ≤ γ →
          ∀ (κ : γ.ToType → Cardinal.{u}), (∀ α, (r : Cardinal.{u}) < κ α) →
            cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ (fun α => κ α + 1) →
            cardinalPartitionRel lam r γ κ
    )

end Problem
