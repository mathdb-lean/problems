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

- problem_id: NElliottHalberstamConjecture_elliott_halberstam
- collection: wikipedia
- question_id: wikipedia:ElliottHalberstamConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/ElliottHalberstamConjecture.lean#elliott_halberstam
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The Elliott–Halberstam conjecture: for every $\theta < 1$ and $A > 0$ there exists a constant $C > 0$ such that $$\sum_{1 \le q \le x^{\theta}} E(x; q) \le \frac{C x}{\log^A x}$$ for all $x > 2$.
- notes: Wikipedia: ElliottHalberstamConjecture -- https://en.wikipedia.org/wiki/Elliott%E2%80%93Halberstam_conjecture
- track: open
- answer_shape: proof
- source_stem: ElliottHalberstamConjecture
- source_namespace: ElliottHalberstamConjecture
- source_theorem: elliott_halberstam
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
$\pi(x; q, a)$: the number of primes $p \le x$ with $p \equiv a \pmod q$.
-/
def primesInAPCount (x q : ℕ) (a : ZMod q) : ℕ :=
  ((Finset.range (x + 1)).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = a).card

/--
The error term
$$E(x; q) = \max_{\gcd(a,q)=1} \left|\pi(x;q,a) - \frac{\pi(x)}{\varphi(q)}\right|,$$
measuring the deviation of the primes in the arithmetic progressions modulo $q$ from
uniform distribution among the $\varphi(q)$ coprime residue classes.
-/
noncomputable def E (x q : ℕ) : ℝ :=
  ⨆ a : (ZMod q)ˣ, |(primesInAPCount x q a : ℝ) - (x.primeCounting : ℝ) / (q.totient : ℝ)|

abbrev Target : Prop :=
    ∀ (θ : ℝ) (hθ : θ < 1) (A : ℝ) (hA : 0 < A),
      ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
        ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, E x q ≤ C * x / Real.log x ^ A

end Problem
