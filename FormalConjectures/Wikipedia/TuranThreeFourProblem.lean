/-
Copyright 2026 The Formal Conjectures Authors.

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

import FormalConjecturesUtil

/-!
# Turán's (3,4)-problem

Turán's 1941 problem asks for the maximum number $\operatorname{ex}_3(n, K_4^{(3)})$ of edges
of a 3-uniform hypergraph on $n$ vertices containing no copy of the complete 3-uniform
hypergraph $K_4^{(3)}$ on four vertices (the "tetrahedron"), i.e. no four vertices spanning
all four possible triples.

The normalized sequence $\operatorname{ex}_3(n, K_4^{(3)})/\binom{n}{3}$ is non-increasing
(Katona–Nemetz–Simonovits [KNS64]), so it converges to the *Turán density* $\pi(K_4^{(3)})$.
Turán's construction — partition the vertices into three near-equal parts $X_1, X_2, X_3$ and
take all triples meeting each part once, together with all triples with two vertices in $X_i$
and one in $X_{i+1}$ (indices cyclic) — shows $\pi(K_4^{(3)}) \geq 5/9$, and Turán conjectured
that equality holds. The best known upper bound, obtained by Razborov via flag algebras, is
$\pi(K_4^{(3)}) \leq 0.561666$ [Ra10]. The conjecture is open; Erdős offered $1000 for its
resolution.

Equivalently (by complementation), the conjecture determines the asymptotics of the covering
Turán number $T(n, 4, 3)$: the minimum number of triples needed so that every four vertices
contain at least one chosen triple.

*References:*
- [Wikipedia, Turán number](https://en.wikipedia.org/wiki/Tur%C3%A1n_number)
- [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
- [Tu41] Turán, Paul, *Egy gráfelméleti szélsőértékfeladatról*, Mat. Fiz. Lapok **48** (1941),
  436–452.
- [KNS64] Katona, Gyula and Nemetz, Tibor and Simonovits, Miklós, *On a problem of Turán in
  the theory of graphs*, Mat. Lapok **15** (1964), 228–238.
- [Ra10] Razborov, Alexander A., *On 3-hypergraphs with forbidden 4-vertex configurations*,
  SIAM J. Discrete Math. **24** (2010), 946–963.
- [Ke11] Keevash, Peter, *Hypergraph Turán problems*, Surveys in Combinatorics 2011,
  London Math. Soc. Lecture Note Ser. **392**, Cambridge Univ. Press (2011), 83–139.
-/

open Filter Finset
open scoped Topology

namespace TuranThreeFourProblem

/-- A finite family `E` of finsets of vertices is a **3-uniform hypergraph** (3-graph) if
every edge is a 3-element set. -/
def IsThreeUniform {V : Type*} (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, e.card = 3

/-- A family `E` of triples is **$K_4^{(3)}$-free** if no four vertices span all four possible
triples: for every 4-element vertex set `s`, at least one 3-element subset of `s` is not an
edge. This is ordinary subgraph-freeness (not induced-subgraph-freeness). -/
def IsK43Free {V : Type*} (E : Finset (Finset V)) : Prop :=
  ∀ s : Finset V, s.card = 4 → ¬ Finset.powersetCard 3 s ⊆ E

/-- The **Turán number** $\operatorname{ex}_3(n, K_4^{(3)})$: the maximum number of edges of a
$K_4^{(3)}$-free 3-uniform hypergraph on `n` vertices. -/
noncomputable def exK43 (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ E : Finset (Finset (Fin n)), IsThreeUniform E ∧ IsK43Free E ∧ E.card = m}

/-- The **covering Turán number** $T(n, 4, 3)$: the minimum number of triples on `n` vertices
such that every 4-element vertex set contains at least one of them. This is the quantity in
Turán's complementary formulation of the problem. -/
noncomputable def coveringT43 (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ E : Finset (Finset (Fin n)), IsThreeUniform E ∧
    (∀ s : Finset (Fin n), s.card = 4 → ∃ e ∈ E, e ⊆ s) ∧ E.card = m}

/-! ## Basic API -/

/-- A 3-uniform hypergraph on `n` vertices has at most $\binom{n}{3}$ edges. -/
@[category API, AMS 5]
theorem IsThreeUniform.card_le_choose {n : ℕ} {E : Finset (Finset (Fin n))}
    (hE : IsThreeUniform E) : E.card ≤ n.choose 3 := by
  have hsub : E ⊆ Finset.powersetCard 3 (univ : Finset (Fin n)) := fun e he ↦
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hE e he⟩
  calc E.card ≤ (Finset.powersetCard 3 (univ : Finset (Fin n))).card :=
        Finset.card_le_card hsub
    _ = n.choose 3 := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The empty hypergraph is $K_4^{(3)}$-free. -/
@[category API, AMS 5]
theorem isK43Free_empty {V : Type*} : IsK43Free (∅ : Finset (Finset V)) := by
  intro s hs hsub
  obtain ⟨t, hts, htcard⟩ := s.exists_smaller_set 3 (by omega)
  simpa using hsub (Finset.mem_powersetCard.mpr ⟨hts, htcard⟩)

/-- The set of edge counts of $K_4^{(3)}$-free 3-graphs on `n` vertices is bounded above. -/
@[category API, AMS 5]
theorem bddAbove_setOf_isK43Free (n : ℕ) :
    BddAbove {m : ℕ | ∃ E : Finset (Finset (Fin n)),
      IsThreeUniform E ∧ IsK43Free E ∧ E.card = m} := by
  refine ⟨n.choose 3, ?_⟩
  rintro m ⟨E, hE, -, rfl⟩
  exact hE.card_le_choose

/-- Every $K_4^{(3)}$-free 3-graph on `n` vertices witnesses a lower bound for the Turán
number `exK43 n`. -/
@[category API, AMS 5]
theorem le_exK43 {n : ℕ} (E : Finset (Finset (Fin n))) (hE : IsThreeUniform E)
    (hfree : IsK43Free E) : E.card ≤ exK43 n :=
  le_csSup (bddAbove_setOf_isK43Free n) ⟨E, hE, hfree, rfl⟩

/-- The Turán number is attained by some extremal $K_4^{(3)}$-free 3-graph. -/
@[category API, AMS 5]
theorem exists_extremal (n : ℕ) :
    ∃ E : Finset (Finset (Fin n)), IsThreeUniform E ∧ IsK43Free E ∧ E.card = exK43 n :=
  Nat.sSup_mem ⟨0, ∅, fun e he ↦ by simp at he, isK43Free_empty, Finset.card_empty⟩
    (bddAbove_setOf_isK43Free n)

/-- The trivial upper bound $\operatorname{ex}_3(n, K_4^{(3)}) \leq \binom{n}{3}$. -/
@[category API, AMS 5]
theorem exK43_le_choose (n : ℕ) : exK43 n ≤ n.choose 3 := by
  unfold exK43
  apply csSup_le ⟨0, ∅, fun e he ↦ by simp at he, isK43Free_empty, Finset.card_empty⟩
  rintro m ⟨E, hE, -, rfl⟩
  exact hE.card_le_choose

/-! ## Sanity checks -/

/-- The complete 3-graph on four vertices is not $K_4^{(3)}$-free. -/
@[category test, AMS 5]
theorem not_isK43Free_complete :
    ¬ IsK43Free (Finset.powersetCard 3 (univ : Finset (Fin 4))) := fun h ↦
  h univ (by simp) subset_rfl

/-- On three vertices there is no room for a $K_4^{(3)}$, so the unique triple can be taken:
$\operatorname{ex}_3(3, K_4^{(3)}) = 1$. -/
@[category test, AMS 5]
theorem exK43_three : exK43 3 = 1 := by
  refine le_antisymm ((exK43_le_choose 3).trans_eq (by decide)) ?_
  have huni : IsThreeUniform ({univ} : Finset (Finset (Fin 3))) := by
    intro e he
    rw [Finset.mem_singleton] at he
    subst he
    simp
  have hfree : IsK43Free ({univ} : Finset (Finset (Fin 3))) := by
    intro s hs _
    have hle := Finset.card_le_univ s
    rw [Finset.card_univ, Fintype.card_fin] at hle
    omega
  simpa using le_exK43 {univ} huni hfree

/-! ## Main problem -/

/--
**Turán's (3,4)-problem (1941) [Tu41]**: determine the Turán density
$$\pi(K_4^{(3)}) = \lim_{n \to \infty} \frac{\operatorname{ex}_3(n, K_4^{(3)})}{\binom{n}{3}}.$$
Turán conjectured that the value is $5/9$; Erdős offered $1000 for a resolution. The limit
exists by [KNS64] (see `turan_three_four_problem.variants.limit_exists`), and the known bounds
are $5/9 \leq \pi(K_4^{(3)}) \leq 0.561666$ [Tu41, Ra10].
-/
@[category research open, AMS 5]
theorem turan_three_four_problem :
    Tendsto (fun n : ℕ ↦ (exK43 n : ℝ) / (n.choose 3 : ℝ)) atTop (𝓝 answer(sorry)) := by
  sorry

/--
**Turán's conjecture on $K_4^{(3)}$ [Tu41]**: is the Turán density of the tetrahedron equal
to $5/9$, i.e. does
$$\operatorname{ex}_3(n, K_4^{(3)}) = \left(\tfrac{5}{9} + o(1)\right)\binom{n}{3}?$$
The lower bound $\pi(K_4^{(3)}) \geq 5/9$ is given by Turán's construction
(`turan_three_four_problem.variants.turan_lower_bound`), so the content of the question is
whether the matching upper bound holds.
-/
@[category research open, AMS 5]
theorem turan_three_four_problem.variants.density_eq_five_ninths : answer(sorry) ↔
    Tendsto (fun n : ℕ ↦ (exK43 n : ℝ) / (n.choose 3 : ℝ)) atTop (𝓝 (5 / 9)) := by
  sorry

/--
The $\varepsilon$-form of Turán's conjecture, stated directly in terms of hypergraphs: is it
true that for every $\varepsilon > 0$ and every sufficiently large $n$, every $K_4^{(3)}$-free
3-uniform hypergraph on $n$ vertices has at most
$\left(\tfrac{5}{9} + \varepsilon\right)\binom{n}{3}$ edges?

Together with Turán's construction this is equivalent to
`turan_three_four_problem.variants.density_eq_five_ninths`.
-/
@[category research open, AMS 5]
theorem turan_three_four_problem.variants.eventual_upper_bound : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ E : Finset (Finset (Fin n)), IsThreeUniform E → IsK43Free E →
        (E.card : ℝ) ≤ (5 / 9 + ε) * (n.choose 3 : ℝ) := by
  sorry

/--
**Turán's exact conjecture [Tu41]**: for $n = 3k$ vertices, is the maximum number of edges of
a $K_4^{(3)}$-free 3-graph exactly $$\frac{k^2(5k-3)}{2},$$ the number of edges of Turán's
construction with three equal parts of size $k$? (Stated multiplied by 2 to avoid natural
number division.) This has been verified for small $n$; it implies
`turan_three_four_problem.variants.density_eq_five_ninths`.
-/
@[category research open, AMS 5]
theorem turan_three_four_problem.variants.exact_value : answer(sorry) ↔
    ∀ k : ℕ, 1 ≤ k → 2 * exK43 (3 * k) = k ^ 2 * (5 * k - 3) := by
  sorry

/-! ## Known results -/

/--
**Katona–Nemetz–Simonovits [KNS64]**: the sequence
$\operatorname{ex}_3(n, K_4^{(3)})/\binom{n}{3}$ is non-increasing in $n \geq 3$, hence the
Turán density $\pi(K_4^{(3)})$ exists.
-/
@[category research solved, AMS 5]
theorem turan_three_four_problem.variants.limit_exists :
    ∃ x : ℝ, Tendsto (fun n : ℕ ↦ (exK43 n : ℝ) / (n.choose 3 : ℝ)) atTop (𝓝 x) := by
  sorry

/--
**Turán's construction [Tu41]**: partitioning the vertex set into three near-equal parts
$X_1, X_2, X_3$ and taking all triples meeting each part once together with all triples having
two vertices in $X_i$ and one in $X_{i+1}$ (indices cyclic) yields a $K_4^{(3)}$-free 3-graph
with $\left(\tfrac{5}{9} - o(1)\right)\binom{n}{3}$ edges. Hence $\pi(K_4^{(3)}) \geq 5/9$.
-/
@[category research solved, AMS 5]
theorem turan_three_four_problem.variants.turan_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ (exK43 n : ℝ) := by
  sorry

/--
**Razborov's flag algebra bound [Ra10]**: $\pi(K_4^{(3)}) \leq 0.561666$. This is the best
known upper bound up to small subsequent numerical improvements; it remains far from the
conjectured value $5/9 = 0.555\ldots$.
-/
@[category research solved, AMS 5]
theorem turan_three_four_problem.variants.razborov_upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (exK43 n : ℝ) ≤ (0.561666 + ε) * (n.choose 3 : ℝ) := by
  sorry

/--
**Complementary formulation**: taking complements within the full triple system exchanges
maximizing edges of a $K_4^{(3)}$-free 3-graph with minimizing a family of triples meeting
every 4-set, giving the exact identity
$$\operatorname{ex}_3(n, K_4^{(3)}) + T(n, 4, 3) = \binom{n}{3}.$$
In particular Turán's conjecture is equivalent to
$T(n, 4, 3) = \left(\tfrac{4}{9} + o(1)\right)\binom{n}{3}$.
-/
@[category textbook, AMS 5]
theorem turan_three_four_problem.variants.covering_identity (n : ℕ) :
    exK43 n + coveringT43 n = n.choose 3 := by
  sorry

end TuranThreeFourProblem
