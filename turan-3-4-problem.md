# Turán’s \((3,4)\)-Problem

## Definitions

A **3-uniform hypergraph**, or **3-graph**, is a pair

\[
H=(V,E),
\]

where \(V\) is a finite vertex set and

\[
E\subseteq \binom{V}{3}.
\]

Thus every edge is a three-element subset of \(V\). All hypergraphs in this problem are simple. Write

\[
e(H)=|E|
\]

for the number of edges of \(H\).

Let \(K_4^3\) denote the complete 3-graph on four vertices:

\[
K_4^3=
\left(
\{1,2,3,4\},
\bigl\{
\{1,2,3\},
\{1,2,4\},
\{1,3,4\},
\{2,3,4\}
\bigr\}
\right).
\]

When no ambiguity arises, an edge such as \(\{1,2,3\}\) may be abbreviated as \(123\).

A 3-graph \(H\) is **\(K_4^3\)-free** if no four vertices of \(H\) span all four possible 3-edges. This is ordinary subgraph-freeness, not induced-subgraph-freeness: a copy of \(K_4^3\) occurs precisely when all four triples on some four vertices are present.

For every integer \(n\ge 4\), define the extremal number

\[
\operatorname{ex}_3(n,K_4^3)
=
\max\left\{
e(H):
|V(H)|=n
\text{ and }
H\text{ is }K_4^3\text{-free}
\right\}.
\]

In other words, \(\operatorname{ex}_3(n,K_4^3)\) is the maximum number of edges in an \(n\)-vertex \(K_4^3\)-free 3-graph.

## Turán density

Define the Turán density

\[
\pi(K_4^3)
=
\lim_{n\to\infty}
\frac{\operatorname{ex}_3(n,K_4^3)}{\binom{n}{3}}.
\]

This limit exists. To see this, let \(n\ge m\ge 4\), and let \(H\) be an \(n\)-vertex \(K_4^3\)-free 3-graph. Every induced subgraph of \(H\) on \(m\) vertices is also \(K_4^3\)-free.

Double-count pairs \((e,S)\), where \(e\in E(H)\), \(S\subseteq V(H)\), \(|S|=m\), and \(e\subseteq S\). This gives

\[
e(H)\binom{n-3}{m-3}
\le
\operatorname{ex}_3(m,K_4^3)\binom{n}{m}.
\]

Taking \(H\) to be extremal and simplifying yields

\[
\frac{\operatorname{ex}_3(n,K_4^3)}{\binom{n}{3}}
\le
\frac{\operatorname{ex}_3(m,K_4^3)}{\binom{m}{3}}.
\]

Therefore the normalized extremal numbers form a non-increasing, nonnegative sequence, so they converge.

## Turán’s construction

Partition an \(n\)-vertex set into three parts

\[
V=X_1\sqcup X_2\sqcup X_3
\]

whose sizes differ by at most one. Interpret the indices cyclically:

\[
X_4=X_1.
\]

Take as edges all triples of either of the following types:

1. Triples containing exactly one vertex from each of \(X_1,X_2,X_3\).

2. Triples containing two vertices from \(X_i\) and one vertex from \(X_{i+1}\), for some \(i\in\{1,2,3\}\).

The cyclic direction matters:

\[
X_1\longrightarrow X_2\longrightarrow X_3\longrightarrow X_1.
\]

If \(x_i=|X_i|\), the construction has exactly

\[
x_1x_2x_3
+
\sum_{i=1}^{3}
\binom{x_i}{2}x_{i+1}
\]

edges.

The construction is \(K_4^3\)-free. Indeed, classify any four vertices by their distribution among the three parts. For each possible distribution—\(4\), \(3+1\), \(2+2\), or \(2+1+1\)—at least one of the four triples fails to satisfy either edge rule. Hence no four vertices span all four possible triples.

Since

\[
x_i=\frac n3+O(1),
\]

we have

\[
x_1x_2x_3
=
\frac{n^3}{27}+O(n^2)
\]

and

\[
\sum_{i=1}^{3}
\binom{x_i}{2}x_{i+1}
=
\frac{n^3}{18}+O(n^2).
\]

Thus the total number of edges is

\[
\frac{5n^3}{54}+O(n^2).
\]

Because

\[
\binom{n}{3}
=
\frac{n^3}{6}+O(n^2),
\]

the construction has

\[
\left(\frac59+o(1)\right)\binom{n}{3}
\]

edges. Consequently,

\[
\pi(K_4^3)\ge \frac59.
\]

## Supplied upper bound

The numerical upper bound supplied with this problem, due to Razborov, is

\[
\pi(K_4^3)\le 0.5611666.
\]

Equivalently,

\[
\operatorname{ex}_3(n,K_4^3)
\le
\left(0.5611666+o(1)\right)\binom{n}{3}.
\]

This is an asymptotic statement. The displayed decimal must not be interpreted as a literal finite-\(n\) bound without an explicit error term.

The supplied bounds are therefore

\[
\frac59
\le
\pi(K_4^3)
\le
0.5611666.
\]

Reproducing this interval is not a resolution of the problem.

# Main problem

Resolve Turán’s problem completely by determining

\[
\boxed{\pi(K_4^3)}.
\]

In particular, decide whether

\[
\boxed{\pi(K_4^3)=\frac59}.
\]

Equivalently, decide whether

\[
\operatorname{ex}_3(n,K_4^3)
=
\left(\frac59+o(1)\right)\binom{n}{3}.
\]

The required conclusion concerns the asymptotic Turán density. An exact formula for \(\operatorname{ex}_3(n,K_4^3)\) for every sufficiently large \(n\), or for every \(n\), would be stronger and should be proved if the method yields one. An asymptotic density calculation alone must not be presented as an exact finite determination.

For purposes of this task, assume that a complete resolution can be found, but do not assume in advance that Turán’s proposed value is true or false.

## What constitutes a complete resolution

A complete solution must prove exactly one of the following alternatives.

### Affirmative resolution

Prove that for every fixed \(\varepsilon>0\), there exists \(n_0(\varepsilon)\) such that every \(K_4^3\)-free 3-graph \(H\) on \(n\ge n_0(\varepsilon)\) vertices satisfies

\[
e(H)
\le
\left(\frac59+\varepsilon\right)\binom{n}{3}.
\]

Together with Turán’s construction, this would prove

\[
\pi(K_4^3)=\frac59
\]

and

\[
\operatorname{ex}_3(n,K_4^3)
=
\left(\frac59+o(1)\right)\binom{n}{3}.
\]

### Negative resolution

Prove that there exists a fixed constant \(\varepsilon>0\) and arbitrarily large integers \(n\) for which there is a \(K_4^3\)-free 3-graph \(H_n\) satisfying

\[
e(H_n)
\ge
\left(\frac59+\varepsilon\right)\binom{n}{3}.
\]

Equivalently, prove

\[
\pi(K_4^3)>\frac59.
\]

Because the normalized extremal numbers converge, these are the only two possibilities.

A negative resolution must establish a fixed positive density gap above \(5/9\). Examples whose densities are only

\[
\frac59+o(1)
\]

do not disprove Turán’s proposed value.

# Equivalent formulations

## Complementary covering formulation

For a 3-graph \(H\) on \(V\), define its complement \(\overline H\) by

\[
E(\overline H)
=
\binom{V}{3}\setminus E(H).
\]

Then \(H\) is \(K_4^3\)-free if and only if every four-element subset of \(V\) contains at least one edge of \(\overline H\).

Define

\[
t_3(n,4)
=
\min\left\{
e(G):
|V(G)|=n
\text{ and every four vertices contain an edge of }G
\right\}.
\]

Then the exact identity

\[
\operatorname{ex}_3(n,K_4^3)
=
\binom{n}{3}-t_3(n,4)
\]

holds for every \(n\).

Consequently, Turán’s proposed value is equivalent to

\[
t_3(n,4)
=
\left(\frac49+o(1)\right)\binom{n}{3}.
\]

Any argument using complements must preserve:

- the reversal between maximizing edges in \(H\) and minimizing edges in \(\overline H\);
- the change from density \(5/9\) to complementary density \(4/9\);
- the direction of every inequality after complementation.

## Link-graph formulation

For \(v\in V(H)\), define the link graph \(L_H(v)\) on \(V(H)\setminus\{v\}\) by

\[
xy\in E(L_H(v))
\quad\Longleftrightarrow\quad
\{v,x,y\}\in E(H).
\]

A four-set \(\{v,a,b,c\}\) spans a copy of \(K_4^3\) precisely when

\[
\{a,b,c\}\in E(H)
\]

and

\[
ab,ac,bc\in E(L_H(v)).
\]

Therefore, for every vertex \(v\), if \(\{a,b,c\}\) is an edge of \(H\) disjoint from \(v\), then \(a,b,c\) cannot form a triangle in \(L_H(v)\).

Equivalently, every triangle in \(L_H(v)\) must correspond to a triple that is absent from \(H\).

This is a joint compatibility condition between \(H\) and all of its link graphs. The individual link graphs:

- are not independently chosen;
- need not be triangle-free;
- cannot be analyzed as arbitrary triangle-free graphs.

# Results that do not constitute a solution

Partial progress is insufficient unless it implies one of the two complete resolutions above. In particular, none of the following is enough:

- Reproducing only the supplied bounds

  \[
  \frac59
  \le
  \pi(K_4^3)
  \le
  0.5611666.
  \]

- Improving the numerical upper bound while leaving it strictly greater than \(5/9\).

- Constructing another family with limiting density exactly \(5/9\), since Turán’s construction already achieves that density.

- Constructing examples whose densities exceed \(5/9\) by quantities tending to zero.

- Proving the conjectured upper bound only along a subsequence of values of \(n\).

- Proving the upper bound only for almost all \(n\).

- Proving the result only for balanced or nearly balanced 3-partite hypergraphs.

- Proving the result only for blow-ups of a fixed finite template.

- Proving the result only within Turán’s cyclic construction, the Turán–Brown–Kostochka constructions, the Fon-der-Flaass constructions, or any other restricted family.

- Proving the result only under an additional forbidden-subgraph, induced-subgraph, minimum-degree, minimum-codegree, quasirandomness, regularity, or symmetry hypothesis.

- Proving an exact result for a related forbidden family, such as \(K_4^3\) together with one or more additional forbidden configurations.

- Assuming without proof that an extremal or near-extremal hypergraph is a blow-up, tripartite, cyclically oriented, homogeneous, vertex-transitive, or isomorphic to a known construction.

- Proving only a stability theorem without using it to derive the sharp global upper bound.

- Identifying candidate extremal limit objects without proving that every admissible limit object has density at most \(5/9\).

- Reducing the problem to a finite optimization problem without proving that the reduction captures every \(K_4^3\)-free 3-graph.

- Obtaining a flag-algebra or semidefinite-programming upper bound that remains strictly greater than \(5/9\).

- Reporting a floating-point semidefinite optimum equal or close to \(5/9\) without a rigorous certificate.

- Using numerical rounding that could conceal a positive error above \(5/9\).

- Checking all \(K_4^3\)-free hypergraphs through any fixed finite number of vertices.

- Proving a result for homomorphism-free hypergraphs without establishing the necessary equivalence with ordinary \(K_4^3\)-subgraph-freeness.

- Confusing induced copies of \(K_4^3\) with ordinary copies.

- Forbidding configurations in which four vertices span exactly three edges rather than all four edges.

- Treating the link graphs as independent.

- Treating every link graph as triangle-free.

- Replacing the normalization \(\binom{n}{3}\) by \(n^3\) without tracking the asymptotic factor of \(6\).

- Confusing the original density \(5/9\) with the complementary density \(4/9\).

- Proving the wrong inequality after passing to the complement.

- Reducing the problem to another unproved extremal, stability, flag-algebra, graphon, hypergraphon, or finite-template statement of comparable strength.

# Permitted methods and standards of proof

Standard proved theorems may be used from areas including:

- extremal hypergraph theory;
- flag algebras;
- graph and hypergraph limits;
- hypergraph regularity and removal theory;
- stability theory;
- Lagrangian methods;
- symmetrization and compression;
- entropy methods;
- semidefinite programming;
- sum-of-squares methods;
- real algebraic geometry;
- probabilistic combinatorics;
- additive combinatorics;
- discrete and continuous optimization.

Every imported theorem must be stated accurately and applied with all required hypotheses, normalizations, error terms, and uniformity conditions.

A computer-assisted proof is permitted, but it must be completely rigorous and independently checkable. In particular:

- every finite case list must be proved exhaustive;
- every numerical inequality must have certified error bounds;
- every reduction from arbitrary hypergraphs to finite data must be justified;
- every semidefinite or flag-algebra calculation must include an exact rational or symbolic certificate, or rigorous interval arithmetic;
- positive semidefiniteness must be proved exactly, not inferred from floating-point eigenvalues;
- no unverified floating-point step may be essential to the conclusion.

# Multi-agent research protocol

Use multi-agent v2 aggressively and dynamically, with up to four concurrent agents.

## Maintain a diverse portfolio

Begin with genuinely different proof and counterexample strategies. Relevant approach families include:

- complement-covering formulations;
- link-graph and codegree methods;
- induction and vertex deletion;
- symmetrization and compression;
- stability approaches;
- hypergraphons and limit objects;
- Lagrangians and blow-ups;
- finite-template searches;
- probabilistic constructions;
- algebraic constructions;
- oriented-graph constructions;
- entropy arguments;
- regularity and removal methods;
- local-density inequalities;
- flag-algebra inequalities;
- exact sum-of-squares certificates;
- SAT, ILP, branch-and-bound, and symmetry-reduced enumeration.

Do not assign every agent to variations of the same strategy. Preserve independence during early exploration so that agents do not all inherit the same unproved structural assumption or converge prematurely on one attractive but incomplete computation.

## Track approach families explicitly

Maintain a registry organized by mathematical mechanism rather than superficial wording. For each route, record:

- its central proposed lemma or construction;
- concrete progress;
- the exact unresolved obstruction;
- whether that obstruction is weaker than, comparable to, or equivalent to the original problem;
- counterexamples found to intermediate claims;
- what new idea would justify reopening the route.

If many agents converge on one approach family, redirect some of them toward underexplored and genuinely incompatible formulations.

## Mark theorem-strength gaps as blocked

A route is blocked if it reduces the problem to an unproved lemma of comparable strength without providing a new mechanism for proving that lemma.

Do not continue assigning agents to a blocked route merely because it reproduces the supplied numerical bound or provides strong evidence for \(5/9\). Reopen it only when an agent proposes a materially new:

- invariant;
- decomposition;
- exact inequality;
- structural theorem;
- certificate;
- construction;
- counterexample;
- proof mechanism.

Keep both sharp-upper-bound routes and positive-density counterexample routes active until one side has been rigorously settled.

## Use computational agents throughout

Computational work should include, where useful:

- enumerating small \(K_4^3\)-free hypergraphs;
- solving exact finite extremal instances by SAT, ILP, or branch-and-bound;
- exploiting isomorphism and symmetry reduction;
- searching finite templates and optimizing their blow-ups;
- running flag-algebra semidefinite programs;
- attempting exact rational reconstruction;
- testing candidate inequalities;
- exploring degree, codegree, and link distributions;
- searching for constructions with density strictly greater than \(5/9\);
- finding counterexamples to proposed intermediate lemmas.

Finite computation is evidence unless it is converted into a rigorous asymptotic proof or an exact certificate completing a valid reduction.

## Require concrete outputs

Agents must return mathematical objects that can be checked, such as:

- precise lemmas;
- explicit constructions;
- exact inequalities;
- degree and codegree identities;
- link-graph constraints;
- flag-algebra expansions;
- positive-semidefinite matrices;
- rational or symbolic certificates;
- quantitative stability statements;
- algorithms and reproducible code outputs;
- exact finite examples;
- counterexamples to proposed sublemmas.

Reject vague status reports, unsupported optimism, and claims that a missing classification, stability, compactness, rounding, or finite-forcibility step is “routine.”

## Adversarial audit requirements

Every candidate proof must be checked for all of the following:

- The hypergraphs are simple and 3-uniform.

- A copy of \(K_4^3\) requires all four triples on the same four vertices.

- Ordinary and induced containment have not been confused.

- Densities are normalized by \(\binom{n}{3}\).

- An affirmative resolution applies to every sufficiently large \(n\), not merely a subsequence or almost all \(n\).

- A negative resolution provides a fixed positive density gap above \(5/9\).

- The cyclic direction in Turán’s construction is preserved.

- Every edge type in Turán’s construction is counted correctly.

- Unequal part sizes are handled when \(3\nmid n\).

- Complementation reverses maxima and minima correctly.

- The densities \(5/9\) and \(4/9\) are not confused.

- Link graphs are not assumed to be independent.

- Link graphs are not incorrectly assumed to be triangle-free.

- No hidden minimum-degree, codegree, regularity, symmetry, quasirandomness, or additional-forbidden-subgraph hypothesis has been introduced.

- No unjustified passage has been made from a fixed finite template or its blow-ups to arbitrary hypergraphs.

- Approximate structure has not been used as though it automatically implied the sharp density bound.

- All error terms are uniform in every relevant auxiliary parameter.

- Limits in \(n\), flag size, regularity scale, truncation order, and semidefinite-relaxation level have not been interchanged without justification.

- Floating-point output has not been presented as an exact certificate.

- Positive semidefiniteness has not been asserted solely from numerical evidence.

- Finite enumeration has not been presented as an asymptotic proof.

- A stability result has not been presented as extremality without a rigorous argument closing the remaining density gap.

- No structural or analytic statement equivalent to

  \[
  \pi(K_4^3)=\frac59
  \]

  has been used circularly.

## Iteration and synthesis

The root agent should repeatedly:

1. Synthesize concrete results from the active approaches.
2. Subject proposed proofs and constructions to adversarial audit.
3. Redirect agents away from duplicated or blocked routes.
4. Cross-pollinate ideas only after independent approaches have developed enough to reveal their true strengths and gaps.
5. Launch new rounds using materially different mechanisms when current routes stall.
6. Preserve multiple incompatible proof routes until a complete resolution survives audit.

Do not stop after the first wave of approaches fails.

# Termination condition

Return a claimed solution only after proving one of the following and successfully auditing every step:

\[
\pi(K_4^3)=\frac59,
\]

or

\[
\pi(K_4^3)>\frac59.
\]

Do not return any of the following as a solution:

- the currently supplied interval;
- a numerical improvement that does not reach \(5/9\);
- a theorem for a restricted class;
- a stability conjecture;
- a finite computation without a complete asymptotic reduction;
- an uncertified semidefinite calculation;
- another construction of density \(5/9\);
- a construction exceeding \(5/9\) only by \(o(1)\);
- a reduction to an isolated missing lemma;
- a best-effort research summary;
- an explanation that the problem is difficult.

If current routes fail, continue by auditing the failures, identifying their precise obstructions, and developing genuinely new approaches. Reopen a blocked route only when there is a materially new mechanism for overcoming its obstruction.

# Public-search restriction

Public search may be used only for ordinary mathematical background and standard named theorems. Do not use public search to look for a solution to this exact Turán problem or benchmark, merely to determine its research status, or as a substitute for constructing and verifying the required proof.
