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

- problem_id: NSparseRuler_wichmann_conjecture
- collection: wikipedia
- question_id: wikipedia:SparseRuler
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/SparseRuler.lean#wichmann_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Wichmann's conjecture on optimal rulers.** Every optimal ruler of sufficiently large length is a Wichmann ruler $W(r, s)$ (up to reflection, i.e. reversing the segment list). Posed by Wichmann [Wi63]. The Wikipedia article records that no optimal ruler of length $1, 13, 17, 23$ or $58$ is a Wichmann ruler, and that every other optimal length up to $213$ is attained by one; non-Wichmann optimal rulers also occur alongside Wichmann ones at lengths $9, 29, 50$ and $68$.
- notes: Wikipedia: SparseRuler -- https://en.wikipedia.org/wiki/Sparse_ruler
- track: open
- answer_shape: proof
- source_stem: SparseRuler
- source_namespace: SparseRuler
- source_theorem: wichmann_conjecture
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: wichmannGaps_length wichmannGaps_sum
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- A ruler is described by its list of *segment lengths* (gaps) `g`, so that its marks are
the partial sums $0 = m_0 < m_1 < \cdots < m_n = L$, where $n$ (`g.length`) is the number of
segments and $L$ (`g.sum`) is the length. -/
def marks (g : List ℕ) : Finset ℕ :=
  (Finset.range (g.length + 1)).image (fun i => (g.take i).sum)

/-- A ruler is *complete* (a perfect ruler) if its marks form a difference basis for
$\{0, 1, \ldots, L\}$, i.e. every distance $k \le L$ is the difference of two marks. This is
`Finset.IsDifferenceBasis` applied to the marks. -/
def IsComplete (g : List ℕ) : Prop :=
  (marks g).IsDifferenceBasis (Finset.range (g.sum + 1))

/-- A complete ruler is *minimal* if no complete ruler of the same length $L$ has fewer marks
(equivalently, fewer segments). -/
def IsMinimal (g : List ℕ) : Prop :=
  IsComplete g ∧ ∀ g' : List ℕ, IsComplete g' → g'.sum = g.sum → g.length ≤ g'.length

/-- A complete ruler is *maximal* if no complete ruler with the same number of marks
(equivalently, the same number of segments) has greater length. -/
def IsMaximal (g : List ℕ) : Prop :=
  IsComplete g ∧ ∀ g' : List ℕ, IsComplete g' → g'.length = g.length → g'.sum ≤ g.sum

/-- A ruler is *optimal* if it is both minimal and maximal. -/
def IsOptimal (g : List ℕ) : Prop := IsMinimal g ∧ IsMaximal g

/-- The *Wichmann ruler* $W(r, s)$ [Wi63], given by its segment-length sequence
$$1^r,\; (r+1),\; (2r+1)^r,\; (4r+3)^s,\; (2r+2)^{r+1},\; 1^r,$$
where $a^b$ denotes $b$ consecutive segments of length $a$. -/
def wichmannGaps (r s : ℕ) : List ℕ :=
  List.replicate r 1 ++ [r + 1] ++ List.replicate r (2 * r + 1) ++
    List.replicate s (4 * r + 3) ++ List.replicate (r + 1) (2 * r + 2) ++ List.replicate r 1

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The Wichmann ruler $W(r, s)$ has $4r + s + 2$ segments, hence $4r + s + 3$ marks [Wi63]. -/
@[category API, AMS 5]
lemma wichmannGaps_length (r s : ℕ) : (wichmannGaps r s).length = 4 * r + s + 2 := by
  simp only [wichmannGaps, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

/-- The Wichmann ruler $W(r, s)$ has length $4r(r + s + 2) + 3(s + 1)$ [Wi63]. -/
@[category API, AMS 5]
lemma wichmannGaps_sum (r s : ℕ) :
    (wichmannGaps r s).sum = 4 * r * (r + s + 2) + 3 * (s + 1) := by
  simp only [wichmannGaps, List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil,
    smul_eq_mul]
  ring

abbrev Target : Prop :=
    ∃ N : ℕ, ∀ g : List ℕ, IsOptimal g → N < g.sum →
      ∃ r s : ℕ, g = wichmannGaps r s ∨ g = (wichmannGaps r s).reverse

end Problem
