# Eulerian Walk Existence — `Eulerian_v2_claude.lean`

This file is a concise refactor of the classical Eulerian existence theorem for
finite connected simple graphs. It proves both directions of the parity criterion:

```lean
theorem SimpleGraph.Walk.exists_isEulerian_of_connected_card_oddDegree_eq_zero_or_two
    (hconn : G.Connected)
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 0 ∨
      Fintype.card {v : V | Odd (G.degree v)} = 2) :
    ∃ u v, ∃ p : G.Walk u v, p.IsEulerian
```

> If `G` is a finite connected simple graph in which either zero or exactly two
> vertices have odd degree, then `G` has an Eulerian walk.

The file is intended as a Mathlib PR candidate. Compared to the predecessor
`Eulerian.lean` (1281 lines), it is **629 lines**: roughly half the size with no
new mathematics, achieved by:

1. unifying the three "longest trail of some kind" constructions behind a single
   helper `exists_maximal_walk`, parameterised by an arbitrary walk predicate;
2. exposing a bundled API (`IsMaximalTrail.*`, `IsMaximalAvoidingFrom.*`)
   instead of repeatedly destructuring `Prop`-conjunctions;
3. replacing the 80-line "two odd vertices ⇒ all others even" cardinality
   bookkeeping with a 15-line `Finset.card_insert_of_notMem` + `omega` argument;
4. dropping the redundant `MaximalTrailFrom` predicate — start-fixed maximality
   is recovered inline by instantiating the generic helper.

---

## Main theorems (public API)

```lean
theorem exists_isEulerian_of_connected_card_oddDegree_eq_zero_or_two
theorem exists_isEulerian_of_connected_forall_even_degree
theorem exists_isEulerian_of_connected_card_oddDegree_eq_two
```

The first is the main result; the latter two are the two cases of the parity
criterion, exposed separately because each is independently useful.

A few derived public theorems may also be of independent interest:

```lean
theorem IsTrail.exists_longer_of_unused_edge_at_start
theorem IsTrail.length_edges_le_card_edgeFinset
theorem IsTrail.odd_countP_edges_right_of_ne
theorem IsMaximalTrail.isEulerian_of_connected_of_closed
```

Everything else is `private` and kept inside the file.

---

## Architecture

The file is divided into three layers.

### 1. Trail-extension primitives

```lean
IsTrail.exists_longer_of_unused_edge_at_start :
    p.IsTrail → G.Adj u v → s(u, v) ∉ p.edges →
    ∃ q : G.Walk u w, q.IsTrail ∧ p.edges.length < q.edges.length
```

A trail can be extended by one unused incident edge at its start.

```lean
IsTrail.exists_longer_of_unused_closed_detour :
    p.IsTrail → x ∈ p.support → c.IsTrail →
    c.edges ≠ [] → c.edges.Disjoint p.edges →
    ∃ q : G.Walk u v, q.IsTrail ∧ p.edges.length < q.edges.length
```

A trail can also be extended by splicing in a *closed* sub-trail at any support
vertex, provided the sub-trail uses only unused edges. This is the
**append-and-stay-a-trail** lemma needed for the two-odd-vertex case.

### 2. Maximal trails: the unified existence engine

The classical proof needs three flavours of "length-maximal trail":

* trails maximal among all trails in `G` (used in both cases);
* trails maximal among those starting at a fixed vertex (used to reason about
  the endpoint of a non-closed maximal trail);
* trails maximal among those starting at a fixed vertex *and avoiding the
  edges of some other walk* (used in the two-odd case).

All three are obtained from one generic lemma:

```lean
private exists_maximal_walk
    (P : ∀ ⦃x y⦄, G.Walk x y → Prop) (u₀ : V)
    (hnil : P (nil : G.Walk u₀ u₀))
    (hP_trail : ∀ ⦃x y⦄ (p : G.Walk x y), P p → p.IsTrail) :
    ∃ x y, ∃ p : G.Walk x y, P p ∧
      ∀ ⦃a b⦄ (q : G.Walk a b), P q → q.edges.length ≤ p.edges.length
```

Proof: filter `Finset.range (G.edgeFinset.card + 1)` by "is the length of some
`P`-walk", take `Finset.max'`, unpack the witness from `Finset.max'_mem`. Trail
length is bounded by edge count via `IsTrail.length_edges_le_card_edgeFinset`.

Both maximal-trail predicates are then defined as bundled `Prop`s with their own
namespaces:

```lean
def IsMaximalTrail (p : G.Walk u v) : Prop :=
  p.IsTrail ∧ ∀ ⦃x y⦄ (q : G.Walk x y), q.IsTrail →
    q.edges.length ≤ p.edges.length

private def IsMaximalAvoidingFrom (p : G.Walk u v) (q : G.Walk x z) : Prop :=
  q.IsTrail ∧ q.edges.Disjoint p.edges ∧
    ∀ ⦃w⦄ (r : G.Walk x w), r.IsTrail → r.edges.Disjoint p.edges →
      r.edges.length ≤ q.edges.length
```

Each carries projection lemmas (`isTrail`, `length_le`, ...) so the rest of the
file never destructures a `⟨_, _, _⟩` again.

### 3. The two cases of the parity theorem

The proof splits on `hodd`.

#### Case 1 — zero odd-degree vertices

* `IsMaximalTrail.isClosed_of_forall_even_degree`:
  a maximal trail in an all-even graph must be closed (its endpoint is forced
  to be odd-incident otherwise).
* `IsMaximalTrail.isEulerian_of_connected_of_closed`:
  in a connected graph, a closed maximal trail is Eulerian — connectedness +
  rotation lets us extend it by any unused incident edge, contradicting
  maximality.
* `exists_isEulerian_of_connected_forall_even_degree` assembles these.

#### Case 2 — exactly two odd-degree vertices

This is the harder case. The endpoints of a maximal trail are forced to be the
two odd-degree vertices (`IsMaximalTrail.not_closed_of_card_odd_degree_eq_two`),
so the trail is *not* closed and rotation is unavailable. Instead we extend by
a **closed detour**:

* `IsMaximalAvoidingFrom.isClosed_of_endpoints`:
  the maximal trail that starts at a support vertex `x` and avoids `p.edges`
  must be closed, by a parity argument on incident-edge counts.
* `IsMaximalAvoidingFrom.length_pos_of_unused_adj_start`:
  if there is an unused edge incident to `x`, that closed detour is nonempty.
* `IsTrail.exists_longer_of_unused_closed_detour`:
  splice the closed detour into `p` at `x` — yields a strictly longer trail.

The parity argument is the technical core of this case. For a trail `p` with
two odd endpoints `u ≠ v`, Mathlib's `IsTrail.even_countP_edges_iff` says

```
Even (p.edges.countP (z ∈ ·))  ↔  z ≠ u ∧ z ≠ v
```

Combined with "the two odd-degree vertices are exactly `u` and `v`", this gives

```
Even (p.edges.countP (z ∈ ·))  ↔  Even (G.degree z)
```

(`IsTrail.even_countP_iff_even_degree_of_endpoints`). For a maximal avoiding-`p`
trail `q : G.Walk x z`, the edges of `q` incident to `z` are exactly the
*unused* incident edges of `z` (using maximality, via
`IsMaximalAvoidingFrom.filter_edgesFinset_eq_incidenceFinset_inter_unused`).
Splitting `G.incidenceFinset z` into used vs unused gives

```
(used at z) + (unused at z) = degree z
```

with `(used at z) = countP (z ∈ ·) p.edges` and `(unused at z) = countP (z ∈ ·) q.edges`.
Since `(used at z)` has the same parity as `degree z`, `(unused at z)` is even
(`IsMaximalAvoidingFrom.even_countP_edges_right_of_endpoints`), hence `x = z`.

Then `exists_isEulerian_of_connected_card_oddDegree_eq_two` puts it together:
take a globally maximal trail, observe its endpoints must be the two odd
vertices, suppose some edge `e` is missing, build a closed disjoint detour at a
support vertex incident to `e`, splice it in, contradict maximality.

---

## Dependency graph

```text
exists_isEulerian_of_connected_card_oddDegree_eq_zero_or_two
├─ exists_isEulerian_of_connected_forall_even_degree           -- Case 1
│  ├─ exists_isMaximalTrail
│  │  └─ exists_maximal_walk
│  │     └─ IsTrail.length_edges_le_card_edgeFinset
│  ├─ IsMaximalTrail.isClosed_of_forall_even_degree
│  │  └─ IsMaximalTrail.odd_degree_right_of_ne
│  │     ├─ IsMaximalTrail.countP_edges_right_eq_degree
│  │     │  └─ IsMaximalTrail.filter_edgesFinset_eq_incidenceFinset
│  │     │     ├─ exists_adj_of_mem_edgeSet_and_mem
│  │     │     └─ IsMaximalTrail.not_unused_edge_at_end
│  │     │        └─ IsTrail.exists_longer_of_unused_edge_at_start
│  │     └─ IsTrail.odd_countP_edges_right_of_ne
│  └─ IsMaximalTrail.isEulerian_of_connected_of_closed
│     ├─ exists_unused_incident_edge_of_unused_edge
│     │  └─ exists_unused_incident_edge_of_walk_to_not_support
│     └─ IsTrail.exists_longer_of_unused_edge_at_start
└─ exists_isEulerian_of_connected_card_oddDegree_eq_two        -- Case 2
   ├─ exists_isMaximalTrail
   ├─ IsMaximalTrail.not_closed_of_card_odd_degree_eq_two
   │  └─ IsMaximalTrail.isEulerian_of_connected_of_closed (closed-case contradiction)
   ├─ IsMaximalTrail.odd_degree_left_of_ne / odd_degree_right_of_ne
   └─ IsMaximalTrail.mem_edges_of_connected_card_two
      ├─ exists_unused_closed_detour
      │  ├─ exists_unused_incident_edge_of_unused_edge
      │  ├─ all_non_endpoint_even_of_card_odd_degree_eq_two
      │  ├─ exists_isMaximalAvoidingFrom
      │  │  └─ exists_maximal_walk
      │  ├─ IsMaximalAvoidingFrom.length_pos_of_unused_adj_start
      │  └─ IsMaximalAvoidingFrom.isClosed_of_endpoints
      │     └─ IsMaximalAvoidingFrom.even_countP_edges_right_of_endpoints
      │        ├─ IsTrail.even_countP_iff_even_degree_of_endpoints
      │        ├─ IsTrail.filter_edgesFinset_eq_incidenceFinset_inter_used
      │        └─ IsMaximalAvoidingFrom.filter_edgesFinset_eq_incidenceFinset_inter_unused
      │           └─ IsMaximalAvoidingFrom.not_unused_edge_at_end
      └─ IsTrail.exists_longer_of_unused_closed_detour
```

---

## Notes for the Mathlib PR

The intended public API is small:

```lean
theorem IsTrail.exists_longer_of_unused_edge_at_start
theorem IsTrail.length_edges_le_card_edgeFinset
theorem IsTrail.odd_countP_edges_right_of_ne
def IsMaximalTrail
theorem IsMaximalTrail.isEulerian_of_connected_of_closed
theorem exists_isMaximalTrail
theorem exists_isEulerian_of_connected_forall_even_degree
theorem exists_isEulerian_of_connected_card_oddDegree_eq_two
theorem exists_isEulerian_of_connected_card_oddDegree_eq_zero_or_two
```

Everything else (`exists_maximal_walk`, `IsMaximalAvoidingFrom` and its lemmas,
the parity helpers, the "exactly two odd ⇒ rest even" lemma, …) is `private`.
If reviewers prefer an even smaller surface, `IsMaximalTrail` and its API can
be folded into the proofs and only the four `exists_isEulerian_*` theorems kept
public.

The file imports only

```lean
Mathlib.Combinatorics.SimpleGraph.Trails
Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
```

and uses `open scoped Sym2` for the `s(·, ·)` notation. No new tactic or
typeclass machinery is introduced.

---

## Glossary of key Lean names

| Lean name | Meaning |
|---|---|
| `p.IsTrail` | `p` has no repeated edges |
| `p.IsEulerian` | `p` is an Eulerian walk |
| `p.edges` | list of edges traversed by `p` |
| `p.support` | list of vertices visited by `p` |
| `p.edges.countP (v ∈ ·)` | number of edges of `p` incident to `v` |
| `G.edgeSet` / `G.edgeFinset` | (finite) set of graph edges |
| `G.incidenceFinset v` | edges of `G` incident to `v` |
| `G.degree v` | degree of vertex `v` |
| `G.Connected` | `G` is preconnected and nonempty |
| `p.rotate x hxp` | closed walk `p` rotated to start and end at `x` |
| `IsMaximalTrail p` | `p` is a trail and no trail in `G` is strictly longer |
| `IsMaximalAvoidingFrom p q` | `q` is a trail from a fixed start, avoiding `p.edges`, maximal among such |



# Informal argument

The main argument is the classical Euler theorem proof by maximal trail.

Start with a connected finite graph where the number of odd-degree vertices is either 0 or 2. Pick a trail that is as long as possible: a walk that never repeats an edge, and among all such walks uses the maximum number of edges.

Now argue that this maximal trail must actually use every edge.

Case 1: no odd-degree vertices

Assume every vertex has even degree.

Take a longest trail p. The first key claim is that p must be closed, meaning it starts and ends at the same vertex. Informally, if it ended somewhere different, then at the endpoint the trail would have used an odd number of incident edges, forcing that vertex to have odd degree, contradiction.

So p is a closed trail.

Now suppose p does not use every edge. Since the graph is connected, there is some unused edge that can be reached from the vertices of p. Because p is closed, you can rotate it so it starts at the relevant vertex, then add the unused edge to make a longer trail. That contradicts maximality.

Therefore the longest trail was already Eulerian.

Case 2: exactly two odd-degree vertices

Again take a longest trail p.

A parity argument shows that its two endpoints must be exactly the two odd-degree vertices. So p is not closed: it starts at one odd vertex and ends at the other.

Now suppose some edge is unused. Since the graph is connected, that unused edge is connected to the trail somehow. The proof builds a second trail q using only unused edges, starting from a vertex on p, and chosen as long as possible subject to avoiding the edges of p.

The key parity step says this avoiding trail q must be closed. Intuitively: once you remove the edges already used by p, the remaining unused-edge structure has even degree at the relevant vertices, so a maximal unused trail cannot get stuck at a different endpoint.

Since q is a nonempty closed detour based at a vertex of p, you can splice it into p: follow p until that vertex, go around q, return to the same vertex, then continue along p.

That gives a longer trail than p, contradiction.

So no edge was unused, and p was Eulerian.

In one sentence

Pick the longest possible trail; parity forces its endpoints to behave correctly, and connectedness plus any unused edge would let you extend or splice in a detour, contradicting maximality, so the trail must use every edge.
