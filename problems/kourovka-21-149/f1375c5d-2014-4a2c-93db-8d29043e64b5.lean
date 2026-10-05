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

- problem_id: K21_149
- collection: kourovka
- question_id: kourovka:21_149
- source: formal-conjectures
- source_locator: FormalConjectures/Kourovka/21_149.lean#kourovka_21_149
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there order automorphisms of Dlab groups that are not induced by conjugation by elements of a (possibly bigger) Dlab group? A Dlab group $G$ (on $I$ or on $\overline{\mathbb{R}}$) carries Dlab's order, and $\alpha$ is an automorphism of $G$ that preserves it. The automorphism $\alpha$ is induced by conjugation in a bigger Dlab group $A$ if $G$ embeds into $A$ by an injective homomorphism $e$ and some $u \in A$ satisfies $e(\alpha(f)) = u^{-1} e(f) u$ for all $f \in G$. This includes the inclusions and the order-preserving embeddings of [GYZ]. The slope groups are arbitrary.
- notes: Kourovka Notebook 21_149
- track: solved
- answer_shape: decide
- source_stem: 21_149
- source_namespace: Kourovka.«21.149»
- source_theorem: kourovka_21_149
- source_category: research solved
- source_ams: 6 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Topology

namespace Problem

/--
An order automorphism $f$ of $\mathbb{R}$ is *locally right $H$-linear* if every point has a
right neighbourhood on which $f$ is affine with slope in $H \le \mathbb{R}_{>0}$.
-/
def IsLocallyRightLinear (H : Subgroup NNRealˣ) (f : ℝ ≃o ℝ) : Prop :=
  ∀ a : ℝ, ∃ ε > (0 : ℝ), ∃ h ∈ H, ∀ x : ℝ, a < x → x < a + ε →
    f x = f a + ((h : NNReal) : ℝ) * (x - a)

/--
$A$ is one of the six Dlab groups with slope group $H$. Each consists of the locally right
$H$-linear order automorphisms $f$ with a condition at the ends.

- Four act on $I = [0, 1]$. An order automorphism of $I$ is identified with its extension to
  $\mathbb{R}$ by the identity, so $f$ fixes every point outside $(0, 1)$. The four groups are
  $D_H(I)$ ($f$ is also the identity near $0$ and near $1$), $D_{H*}(I)$ (near $0$),
  $D_{*H}(I)$ (near $1$) and $\overline{D}_H(I)$ (no further condition).
- Two act on the extended real line $\overline{\mathbb{R}}$, whose order automorphisms are those
  of $\mathbb{R}$. They are $D_H$ ($f$ is the identity near $-\infty$ and near $+\infty$) and
  $D_{H*}$ (near $-\infty$).
-/
def IsDlabGroup (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)) : Prop :=
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    (∀ᶠ x in 𝓝 (0 : ℝ), f x = x) ∧ ∀ᶠ x in 𝓝 (1 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    ∀ᶠ x in 𝓝 (0 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    ∀ᶠ x in 𝓝 (1 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ ∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ᶠ x in atBot, f x = x) ∧
    ∀ᶠ x in atTop, f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ ∀ᶠ x in atBot, f x = x)

/--
Dlab's order on a group $G$ of order automorphisms of $\mathbb{R}$: $f < g$ if $f(x) < g(x)$ at
some point $x$ and every point $y$ with $g(y) < f(y)$ lies to the right of $x$. For elements of
a Dlab group, this says that $f$ is below $g$ just after the point where they start to differ.
-/
def DlabLt {G : Subgroup (ℝ ≃o ℝ)} (f g : G) : Prop :=
  ∃ x, (f : ℝ ≃o ℝ) x < (g : ℝ ≃o ℝ) x ∧ ∀ y, (g : ℝ ≃o ℝ) y < (f : ℝ ≃o ℝ) y → x < y

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧
          ∃ α : G ≃* G, (∀ f g : G, DlabLt (α f) (α g) ↔ DlabLt f g) ∧
            ¬ ∃ (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)), IsDlabGroup H A ∧
              ∃ e : G →* A, Function.Injective e ∧ ∃ u : A, ∀ f : G, e (α f) = u⁻¹ * e f * u

end Problem
