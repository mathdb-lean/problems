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

- problem_id: SATSharpness
- collection: openai-math
- question_id: openai-math:235
- source: openai-math
- source_locator: lean/ComparatorChallenges/SATSharpness.lean#OAI.RandomKSAT.sharpness
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For random k-SAT with independent uniformly signed proper clauses sampled with replacement, proves finite positive limiting thresholds and hitting-time variance $`\Theta_k(n)`$ for every fixed k ≥ 3, and computability of the 3-SAT threshold. We credit Gaia Carenini with priority for resolving the threshold-existence conjecture in her concurrent [ECCC TR26-229](https://eccc.weizmann.ac.il/report/2026/229/), made public October 5, 2026; this family supplies another proof and the sharper variance and computability results. ([Lean](lean/docs/235.md)) For every fixed integer k ≥ 3, random k-SAT with independent uniformly signed clauses on distinct variables, sampled with replacement, has a finite positive limiting satisfiability threshold. We credit Gaia Carenini [[5]](https://eccc.weizmann.ac.il/report/2026/229/) with priority for resolving the satisfiability conjecture. This paper gives an alternative proof, using concentration of a capped last satisfiable index and a comparison between different system sizes. Let Hn be the index of the first unsatisfiable prefix in random k-SAT on n variables, with independent uniformly signed clauses using k distinct variables and sampled with replacement. For every fixed k ≥ 4, we prove $`\mathop{\mathrm{Var}}\nolimits (H_n)=\Theta_k(n)`$. For k = 3, the variance is bounded below by a positive multiple of n and above by a constant multiple of $`n\log n`$; the companion paper on random 3-SAT sharpens this to $`\Theta(n)`$. The same upper bounds proved here hold after clipping at any fixed positive multiple of n. The limiting satisfiability threshold of uniform random 3-SAT is a computable real. We credit Gaia Carenini [[4]](https://eccc.weizmann.ac.il/report/2026/229/) with priority for resolving the satisfiability conjecture, which establishes the threshold's existence. We prove that one finite deterministic machine can approximate it to any prescribed accuracy. A deletion estimate gives explicit lower certificates, while a finite hierarchical approximation of the soft pressure gives upper certificates at every larger rational density. A fair search through these certificates halts without requiring a computable rate of finite-size convergence.
- notes: OpenAI math result family 235, Limiting random SAT thresholds, sharp variance and computability -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/235.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.RandomKSAT.sharpness
- source_theorem_count: 1
- source_solution_module: OAI.Probability.SATVariance.Sharpness
- source_papers: preprints/A-Limiting-Satisfiability-Threshold-for-Every-Fixed-Clause-Size-September-25-2026/article.pdf preprints/Variance-of-the-Random-k-SAT-Hitting-Time-September-27-2026/article.pdf preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf
- source_scope_note: lean/docs/235.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

abbrev Assignment (n : ℕ) := Fin n → Bool

def Clause (n k : ℕ) :=
  (s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)

instance clauseFintype (n k : ℕ) : Fintype (Clause n k) := by
  classical
  unfold Clause
  infer_instance

instance clauseMeasurableSpace (n k : ℕ) : MeasurableSpace (Clause n k) := ⊤

instance clauseMeasurableSingletonClass (n k : ℕ) :
    MeasurableSingletonClass (Clause n k) := ⟨fun _ => trivial⟩

def Satisfies {n k : ℕ} (c : Clause n k) (a : Assignment n) : Prop :=
  ∃ v : c.1.1, a v = c.2 v

abbrev Stream (n k : ℕ) := ℕ → Clause n k

def clauseLaw (n k : ℕ) : Measure (Clause n k) := uniformOn Set.univ

def streamLaw (n k : ℕ) : Measure (Stream n k) :=
  Measure.infinitePi (fun _ : ℕ => clauseLaw n k)

def SetSAT {u s : ℕ} (S : Finset (Assignment u)) (ω : Stream u s) (g : ℕ) : Prop :=
  ∃ a ∈ S, ∀ i < g, Satisfies (ω i) a

def blockKill (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) : ℝ :=
  (streamLaw u s {ω | ¬ SetSAT S ω g}).toReal

def favg.{u_1} {α : Type u_1} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

def clauseStep (u s : ℕ) (f : Finset (Assignment u) → ℝ)
    (S : Finset (Assignment u)) : ℝ :=
  favg fun c : Clause u s => f (S.filter (Satisfies c))

def alive (u : ℕ) (S : Finset (Assignment u)) : ℝ := if S.Nonempty then 1 else 0

def survival (u s : ℕ) (S : Finset (Assignment u)) (m : ℕ) : ℝ :=
  (clauseStep u s)^[m] (alive u) S

def lifetime (u s : ℕ) (S : Finset (Assignment u)) : ℝ := ∑' m, survival u s S m

def sharpness_statement : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k),
    (∀ γ D A : ℝ, γ < (k : ℝ) / ((k-1 : ℕ) : ℝ) → 0 < D → 0 < A →
      ∀ N : ℕ, ∃ u : ℕ, N ≤ u ∧ k ≤ u ∧ ∃ S : Finset (Assignment u),
        S.Nonempty ∧ A * (u : ℝ) ^ (-((k-1 : ℕ) : ℝ)) ≤ blockKill u (k-1) S 1 ∧
        D * (blockKill u (k-1) S 1) ^ (-γ) < lifetime u k S) ∧
    (∃ u : ℕ → ℕ, ∃ S : ∀ g, Finset (Assignment (u g)),
      (∀ g, 2 ≤ g → k ≤ u g ∧ (S g).Nonempty) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun g => blockKill (u g) (k-1) (S g) 1 - blockKill (u g) k (S g) g)
        (fun g => ((2 : ℝ)^k)⁻¹ * (g : ℝ)^(-((k-1 : ℕ) : ℝ)))) ∧
    (¬ ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO Filter.atTop e (fun g => (g : ℝ)^(-((k-1 : ℕ) : ℝ))) ∧
      ∀ u, k ≤ u → ∀ S : Finset (Assignment u), S.Nonempty → ∀ g, 2 ≤ g →
        blockKill u (k-1) S 1 - e g ≤ blockKill u k S g)

end RandomKSAT

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.RandomKSAT.sharpness_statement

end Problem

/- Formalization scope, from lean/docs/235.md: The random $k$-SAT threshold problem asks whether satisfiability changes at one limiting clause density. The formalization proves that every fixed integer $k\ge3$ has a finite positive threshold $\alpha_k$: for every fixed density $c<\alpha_k$, the satisfiability probability tends to one as the number of variables grows, while for every $c>\alpha_k$ it tends to zero. Clauses use distinct variables with independent uniform signs and are sampled independently with replacement. The statement makes no assertion at the threshold itself. Let $H_n$ be the first unsatisfiable prefix length in random $k$-SAT with independent uniformly signed clauses on $k$ distinct variables, sampled with replacement. The formalization proves $\mathrm{Var}(H_n)=\Theta_k(n)$ for every fixed $k\ge4$. For $k=3$, it proves a positive linear lower bound and an $O(n\log n)$ upper bound. The same upper bounds hold after clipping at any fixed positive multiple of $n$, and linear lower bounds hold for sufficiently high clipping levels. The linked supplements prove sharpness of the separate survival-lifetime and clause-replacement estimates used in the argument. They do not show that the logarithmic factor in the $k=3$ variance bound is necessary. The formalization proves that the limiting threshold $\alpha$ for uniform random $3$-SAT is a computable positive real. Satisfiability tends to one at every fixed density below $\alpha$ and to zero at every fixed density above it. One deterministic machine produces a rational number $q_r$ for every requested precision $r$ with $|q_r-\alpha|\le2^{-r}$. No computable rate of finite-size convergence is assumed in the statement. -/
