# Eulerian Walk Existence from Connectedness and Even Degrees

This file develops a constructive proof of the standard Eulerian existence theorem for finite connected simple graphs:

```lean
theorem SimpleGraph.Walk.exists_isEulerian_of_connected_forall_even_degree
    (u₀ : V)
    (hconn : G.Connected)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    ∃ u, ∃ p : G.Walk u u, p.IsEulerian
```

In words:

> If `G` is a finite connected simple graph and every vertex has even degree, then `G` has a closed Eulerian walk.

The proof follows the classical maximal-trail argument:

1. Choose a trail of maximal possible length.
2. Show that every maximal trail in an all-even graph must be closed.
3. Show that a closed maximal trail in a connected graph must use every edge.
4. Convert “closed trail using every edge” into `p.IsEulerian`.

The Lean proof is organized around two maximality predicates:

```lean
def MaximalTrailFrom {u v : V} (p : G.Walk u v) : Prop
```

and

```lean
def MaximalTrail {u v : V} (p : G.Walk u v) : Prop
```

`MaximalTrailFrom p` says that `p` is a trail and is length-maximal among trails with the same starting vertex.
`MaximalTrail p` says that `p` is a trail and is globally length-maximal among all trails in the graph.

---

## Main theorem

### `SimpleGraph.Walk.exists_isEulerian_of_connected_forall_even_degree`

```lean
theorem exists_isEulerian_of_connected_forall_even_degree
    (u₀ : V)
    (hconn : G.Connected)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    ∃ u, ∃ p : G.Walk u u, p.IsEulerian
```

This is the final existence theorem.

The proof uses:

- [`exists_closed_maximalTrail_of_forall_even_degree`](#simplegraphwalkexists_closed_maximaltrail_of_forall_even_degree) to obtain a closed globally maximal trail;
- [`MaximalTrail.isEulerian_of_connected`](#simplegraphwalkmaximaltrailiseulerian_of_connected) to prove that this closed maximal trail is Eulerian.

Natural-language proof:

1. By finite maximality, choose a globally maximal trail `p`.
2. Since all degrees are even, `p` must be closed.
3. Since `G` is connected, if `p` missed an edge, then some unused edge would be incident to the support of `p`.
4. Rotating the closed trail to start at that incident vertex and adding the unused edge would produce a strictly longer trail.
5. This contradicts global maximality.
6. Therefore `p` uses every edge.
7. Since `p` is a trail and uses every edge, `p.IsEulerian`.

---

## Local trail-extension lemmas

### `SimpleGraph.Walk.IsTrail.cons_of_unused_edge`

```lean
theorem IsTrail.cons_of_unused_edge
    {u v w : V} {p : G.Walk v w}
    (hp : p.IsTrail)
    (huv : G.Adj u v)
    (hunused : s(u, v) ∉ p.edges) :
    (SimpleGraph.Walk.cons huv p).IsTrail
```

This is a small wrapper around Mathlib’s existing trail constructor:

```lean
SimpleGraph.Walk.IsTrail.cons
```

It says:

> If `p` is a trail and the edge `s(u, v)` is not already used by `p`, then prepending the edge `u -- v` to `p` gives another trail.

This lemma is used by [`IsTrail.exists_longer_of_unused_edge_at_start`](#simplegraphwalkistrail.exists_longer_of_unused_edge_at_start).

---

### `SimpleGraph.Walk.IsTrail.exists_longer_of_unused_edge_at_start`

```lean
theorem IsTrail.exists_longer_of_unused_edge_at_start
    {u v w : V} {p : G.Walk v w}
    (hp : p.IsTrail)
    (huv : G.Adj u v)
    (hunused : s(u, v) ∉ p.edges) :
    ∃ q : G.Walk u w, q.IsTrail ∧ p.edges.length < q.edges.length
```

This is the fundamental “extend a trail by one unused edge” lemma.

It proves:

> If `p` is a trail from `v` to `w`, and there is an unused edge from `u` to `v`, then `cons huv p` is a strictly longer trail from `u` to `w`.

Natural-language proof:

1. Define `q := cons huv p`.
2. By [`IsTrail.cons_of_unused_edge`](#simplegraphwalkistrailcons_of_unused_edge), `q` is a trail.
3. The edge list of `q` is one element longer than the edge list of `p`, so `p.edges.length < q.edges.length`.

This lemma is used twice:

- in [`MaximalTrailFrom.not_unused_edge_at_end`](#simplegraphwalkmaximaltrailfromnot_unused_edge_at_end);
- in [`MaximalTrail.isEulerian_of_connected`](#simplegraphwalkmaximaltrailiseulerian_of_connected).

---

## Maximal trail predicates

### `SimpleGraph.Walk.MaximalTrailFrom`

```lean
def MaximalTrailFrom {u v : V} (p : G.Walk u v) : Prop :=
  p.IsTrail ∧
    ∀ ⦃w : V⦄ (q : G.Walk u w),
      q.IsTrail →
      q.edges.length ≤ p.edges.length
```

`MaximalTrailFrom p` means:

> `p` is a trail, and among all trails that start at the same vertex as `p`, no trail is longer.

This is the right notion for proving that the endpoint of a maximal trail has no unused incident edge.

---

### `SimpleGraph.Walk.MaximalTrail`

```lean
def MaximalTrail {u v : V} (p : G.Walk u v) : Prop :=
  p.IsTrail ∧
    ∀ ⦃x y : V⦄ (q : G.Walk x y),
      q.IsTrail →
      q.edges.length ≤ p.edges.length
```

`MaximalTrail p` means:

> `p` is a trail, and no trail anywhere in the graph is longer.

This is stronger than `MaximalTrailFrom`.

It is used for the connectedness argument: after rotating a closed maximal trail and prepending an unused edge, the resulting trail may start at a different vertex. Global maximality is therefore convenient.

---

### `SimpleGraph.Walk.MaximalTrail.toMaximalTrailFrom`

```lean
theorem MaximalTrail.toMaximalTrailFrom
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p) :
    MaximalTrailFrom p
```

This lemma converts global maximality into start-fixed maximality.

Natural-language proof:

1. `hpmax.1` proves that `p` is a trail.
2. If `q` is any trail starting at the same vertex as `p`, then `q` is also a trail somewhere in the graph.
3. Therefore the global maximality part of `hpmax` gives `q.edges.length ≤ p.edges.length`.

This lemma is used by:

- [`MaximalTrail.isClosed_of_forall_even_degree`](#simplegraphwalkmaximaltrailisclosed_of_forall_even_degree).

---

## Endpoint and parity lemmas

### `SimpleGraph.Walk.MaximalTrailFrom.not_unused_edge_at_end`

```lean
theorem MaximalTrailFrom.not_unused_edge_at_end
    {u v w : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p)
    (hvw : G.Adj v w) :
    s(v, w) ∈ p.edges
```

This lemma proves:

> If `p` is maximal among trails starting at `u`, then every edge incident to its endpoint `v` has already been used by `p`.

Natural-language proof:

1. Suppose `s(v, w)` is not in `p.edges`.
2. Reverse `p`. Since `p` is a trail, `p.reverse` is a trail.
3. The unused edge `s(v, w)` becomes the unused edge `s(w, v)` at the start of `p.reverse`.
4. By [`IsTrail.exists_longer_of_unused_edge_at_start`](#simplegraphwalkistrail.exists_longer_of_unused_edge_at_start), we get a longer trail `q` starting at `w` and ending at `u`.
5. Reverse `q`. Then `q.reverse` is a trail starting at `u`.
6. `q.reverse` is longer than `p`.
7. This contradicts `MaximalTrailFrom p`.

Important Lean ingredients:

- `SimpleGraph.Walk.IsTrail.reverse`;
- `SimpleGraph.Walk.edges_reverse`;
- `List.mem_reverse`;
- `List.length_reverse`;
- [`IsTrail.exists_longer_of_unused_edge_at_start`](#simplegraphwalkistrail.exists_longer_of_unused_edge_at_start).

This lemma is used in:

- [`MaximalTrailFrom.filter_edgesFinset_eq_incidenceFinset`](#simplegraphwalkmaximaltrailfromfilter_edgesfinset_eq_incidencefinset).

---

### `SimpleGraph.Walk.IsTrail.not_even_countP_edges_right_of_ne`

```lean
theorem IsTrail.not_even_countP_edges_right_of_ne
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (huv : u ≠ v) :
    ¬ Even (p.edges.countP fun e => v ∈ e)
```

This lemma says:

> If `p` is a trail from `u` to `v` and `u ≠ v`, then the number of edges of `p` incident to the endpoint `v` is not even.

It uses Mathlib’s parity theorem for trails:

```lean
SimpleGraph.Walk.IsTrail.even_countP_edges_iff
```

That theorem characterizes which vertices have even edge-incidence count along a trail.

Natural-language proof:

1. Assume the count of edges incident to `v` is even.
2. Apply `hp.even_countP_edges_iff v`.
3. Since `u ≠ v`, the theorem implies `v ≠ v`.
4. This is impossible.

This lemma is used by:

- [`IsTrail.odd_countP_edges_right_of_ne`](#simplegraphwalkistrailodd_countp_edges_right_of_ne).

---

### `SimpleGraph.Walk.IsTrail.odd_countP_edges_right_of_ne`

```lean
theorem IsTrail.odd_countP_edges_right_of_ne
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (huv : u ≠ v) :
    Odd (p.edges.countP fun e => v ∈ e)
```

This is the odd-count version of the previous lemma.

It proves:

> If a trail has distinct endpoints, then the number of trail edges incident to the final endpoint is odd.

Natural-language proof:

1. By [`IsTrail.not_even_countP_edges_right_of_ne`](#simplegraphwalkistrailnot_even_countp_edges_right_of_ne), the count is not even.
2. Use `Nat.not_even_iff_odd` to conclude that it is odd.

This lemma is used by:

- [`MaximalTrailFrom.isClosed_of_forall_even_degree`](#simplegraphwalkmaximaltrailfromisclosed_of_forall_even_degree).

---

## Edge-set and incidence lemmas

### `SimpleGraph.Walk.exists_adj_of_mem_edgeSet_and_mem`

```lean
theorem exists_adj_of_mem_edgeSet_and_mem
    {v : V} {e : Sym2 V}
    (heG : e ∈ G.edgeSet)
    (hev : v ∈ e) :
    ∃ w, G.Adj v w ∧ e = s(v, w)
```

This lemma unpacks an edge `e : Sym2 V`.

It proves:

> If `e` is an edge of `G` and `v` is one endpoint of `e`, then the other endpoint can be called `w`, `G.Adj v w`, and `e = s(v, w)`.

Natural-language proof:

1. Induct on the symmetric pair `e` using `Sym2.ind`.
2. Write `e = s(a, b)`.
3. From `e ∈ G.edgeSet`, get `G.Adj a b`.
4. From `v ∈ s(a, b)`, get either `v = a` or `v = b`.
5. In the first case take `w = b`.
6. In the second case take `w = a` and use symmetry of adjacency plus `Sym2.eq_swap`.

Important Lean ingredients:

- `Sym2.ind`;
- `Sym2.mem_iff`;
- `SimpleGraph.mem_edgeSet`;
- `Sym2.eq_swap`.

This lemma is used in:

- [`MaximalTrailFrom.filter_edgesFinset_eq_incidenceFinset`](#simplegraphwalkmaximaltrailfromfilter_edgesfinset_eq_incidencefinset).

---

### `SimpleGraph.Walk.MaximalTrailFrom.filter_edgesFinset_eq_incidenceFinset`

```lean
theorem MaximalTrailFrom.filter_edgesFinset_eq_incidenceFinset
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p) :
    hpmax.1.edgesFinset.filter (fun e => v ∈ e) = G.incidenceFinset v
```

This lemma proves:

> For a start-maximal trail `p : G.Walk u v`, the set of edges of `p` incident to its endpoint `v` is exactly the graph incidence finset at `v`.

This is the key bridge between a count of edges used by the trail and the actual graph degree of `v`.

Natural-language proof:

#### Forward inclusion

If `e` is in the filtered edge finset of `p`, then:

1. `e ∈ hpmax.1.edgesFinset`, so `e ∈ p.edges`.
2. Since every walk edge belongs to the graph edge set, `e ∈ G.edgeSet`.
3. The filter condition gives `v ∈ e`.
4. By `SimpleGraph.incidenceFinset_eq_filter`, this means `e ∈ G.incidenceFinset v`.

#### Reverse inclusion

If `e ∈ G.incidenceFinset v`, then:

1. By `SimpleGraph.incidenceFinset_eq_filter`, we know `e ∈ G.edgeSet` and `v ∈ e`.
2. By [`exists_adj_of_mem_edgeSet_and_mem`](#simplegraphwalkexists_adj_of_mem_edgeset_and_mem), write `e = s(v, w)` with `G.Adj v w`.
3. By [`MaximalTrailFrom.not_unused_edge_at_end`](#simplegraphwalkmaximaltrailfromnot_unused_edge_at_end), the edge `s(v, w)` belongs to `p.edges`.
4. Therefore `e` belongs to `hpmax.1.edgesFinset`.
5. The filter condition is `v ∈ e`, which is immediate.

Important Lean ingredients:

- `SimpleGraph.incidenceFinset_eq_filter`;
- `SimpleGraph.Walk.edges_subset_edgeSet`;
- `SimpleGraph.Walk.IsTrail.edgesFinset`;
- [`exists_adj_of_mem_edgeSet_and_mem`](#simplegraphwalkexists_adj_of_mem_edgeset_and_mem);
- [`MaximalTrailFrom.not_unused_edge_at_end`](#simplegraphwalkmaximaltrailfromnot_unused_edge_at_end).

This lemma is used by:

- [`MaximalTrailFrom.countP_edges_right_eq_degree`](#simplegraphwalkmaximaltrailfromcountp_edges_right_eq_degree).

---

### `SimpleGraph.Walk.MaximalTrailFrom.countP_edges_right_eq_degree`

```lean
theorem MaximalTrailFrom.countP_edges_right_eq_degree
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p) :
    p.edges.countP (fun e => v ∈ e) =
      @SimpleGraph.degree V G v
        (Subtype.fintype (Membership.mem (G.neighborSet v)))
```

This lemma proves:

> For a start-maximal trail ending at `v`, the number of trail edges incident to `v` equals the degree of `v` in the graph.

Natural-language proof:

1. Convert the list count on `p.edges` into a finset/cardinality statement:
   - `Multiset.coe_countP`;
   - `Multiset.countP_eq_card_filter`.
2. Convert the degree of `v` into the cardinality of `G.incidenceFinset v`:
   - `SimpleGraph.card_incidenceFinset_eq_degree`.
3. Use [`MaximalTrailFrom.filter_edgesFinset_eq_incidenceFinset`](#simplegraphwalkmaximaltrailfromfilter_edgesfinset_eq_incidencefinset).

This lemma is used by:

- [`MaximalTrailFrom.isClosed_of_forall_even_degree`](#simplegraphwalkmaximaltrailfromisclosed_of_forall_even_degree).

---

## Closedness of maximal trails in all-even graphs

### `SimpleGraph.Walk.MaximalTrailFrom.isClosed_of_forall_even_degree`

```lean
theorem MaximalTrailFrom.isClosed_of_forall_even_degree
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    u = v
```

This proves:

> In a graph where every vertex has even degree, a trail that is maximal among trails starting at `u` must end at `u`.

Natural-language proof:

1. Suppose, for contradiction, that `u ≠ v`.
2. Since `p` is a trail from `u` to `v`, [`IsTrail.odd_countP_edges_right_of_ne`](#simplegraphwalkistrailodd_countp_edges_right_of_ne) shows that the number of edges of `p` incident to `v` is odd.
3. By [`MaximalTrailFrom.countP_edges_right_eq_degree`](#simplegraphwalkmaximaltrailfromcountp_edges_right_eq_degree), this count equals `G.degree v`.
4. Therefore `G.degree v` is odd.
5. But `heven v` says `G.degree v` is even.
6. Contradiction.

This lemma is used by:

- [`MaximalTrail.isClosed_of_forall_even_degree`](#simplegraphwalkmaximaltrailisclosed_of_forall_even_degree);
- [`exists_closed_maximalTrailFrom_of_forall_even_degree`](#simplegraphwalkexists_closed_maximaltrailfrom_of_forall_even_degree).

---

### `SimpleGraph.Walk.MaximalTrail.isClosed_of_forall_even_degree`

```lean
theorem MaximalTrail.isClosed_of_forall_even_degree
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    u = v
```

This is the global-maximal version of the previous theorem.

Natural-language proof:

1. Convert `MaximalTrail p` into `MaximalTrailFrom p` using [`MaximalTrail.toMaximalTrailFrom`](#simplegraphwalkmaximaltrailtomaximaltrailfrom).
2. Apply [`MaximalTrailFrom.isClosed_of_forall_even_degree`](#simplegraphwalkmaximaltrailfromisclosed_of_forall_even_degree).

---

## Existence of maximal trails

### `SimpleGraph.Walk.IsTrail.length_edges_le_card_edgeFinset`

```lean
theorem IsTrail.length_edges_le_card_edgeFinset
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) :
    p.edges.length ≤ G.edgeFinset.card
```

This lemma proves:

> A trail cannot use more edges than the graph has.

Natural-language proof:

1. Since `p` is a trail, `p.edges` has no duplicates:
   - `hp.edges_nodup`.
2. Therefore `p.edges.length = p.edges.toFinset.card`:
   - `List.toFinset_card_of_nodup`.
3. Every edge of `p` lies in `G.edgeFinset`:
   - `SimpleGraph.Walk.edges_subset_edgeSet`.
4. Thus `p.edges.toFinset ⊆ G.edgeFinset`.
5. Apply `Finset.card_le_card`.

This bound is used to define finite sets of possible trail lengths.

---

### `SimpleGraph.Walk.trailLengthSet`

```lean
noncomputable def trailLengthSet (u : V) : Finset ℕ
```

This finset contains all possible lengths of trails starting at the fixed vertex `u`.

It is defined as a filtered finite range:

```lean
(Finset.range (G.edgeFinset.card + 1)).filter fun n =>
  ∃ v, ∃ p : G.Walk u v, p.IsTrail ∧ p.edges.length = n
```

The range is finite because [`IsTrail.length_edges_le_card_edgeFinset`](#simplegraphwalkistraillength_edges_le_card_edgefinset) bounds every trail length by `G.edgeFinset.card`.

---

### `SimpleGraph.Walk.zero_mem_trailLengthSet`

```lean
theorem zero_mem_trailLengthSet (u : V) :
    0 ∈ trailLengthSet (G := G) u
```

This proves:

> The length set for trails starting at `u` is nonempty.

Natural-language proof:

1. Use the empty walk `SimpleGraph.Walk.nil : G.Walk u u`.
2. It is a trail.
3. Its edge length is `0`.

This lemma is used to define `maxTrailLengthFrom`.

---

### `SimpleGraph.Walk.maxTrailLengthFrom`

```lean
noncomputable def maxTrailLengthFrom (u : V) : ℕ
```

This is the maximum length of any trail starting at `u`.

It is defined using `Finset.max'` on `trailLengthSet u`, whose nonemptiness is provided by [`zero_mem_trailLengthSet`](#simplegraphwalkzero_mem_traillengthset).

---

### `SimpleGraph.Walk.trail_length_le_maxTrailLengthFrom`

```lean
theorem trail_length_le_maxTrailLengthFrom
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) :
    p.edges.length ≤ maxTrailLengthFrom (G := G) u
```

This proves:

> Every trail starting at `u` has length at most `maxTrailLengthFrom u`.

Natural-language proof:

1. Show `p.edges.length ∈ trailLengthSet u`.
2. The range membership follows from [`IsTrail.length_edges_le_card_edgeFinset`](#simplegraphwalkistraillength_edges_le_card_edgefinset).
3. The existential witness is `v, p, hp, rfl`.
4. Apply `Finset.le_max'`.

This lemma is used by:

- [`exists_maximalTrailFrom`](#simplegraphwalkexists_maximaltrailfrom).

---

### `SimpleGraph.Walk.exists_maximalTrailFrom`

```lean
theorem exists_maximalTrailFrom
    (u : V) :
    ∃ v, ∃ p : G.Walk u v, MaximalTrailFrom p
```

This proves:

> For every starting vertex `u`, there exists a trail starting at `u` that is maximal among trails starting at `u`.

Natural-language proof:

1. Let `maxTrailLengthFrom u` be the maximum trail length starting at `u`.
2. Since it belongs to `trailLengthSet u`, unpack a trail `p : G.Walk u v` with that length.
3. Prove `p.IsTrail` from the unpacked witness.
4. For any other trail `q` starting at `u`, use [`trail_length_le_maxTrailLengthFrom`](#simplegraphwalktrail_length_le_maxtraillengthfrom).
5. Rewrite the maximum length using the equality `p.edges.length = maxTrailLengthFrom u`.
6. Conclude `q.edges.length ≤ p.edges.length`.

---

### `SimpleGraph.Walk.exists_closed_maximalTrailFrom_of_forall_even_degree`

```lean
theorem exists_closed_maximalTrailFrom_of_forall_even_degree
    (u : V)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    ∃ p : G.Walk u u, MaximalTrailFrom p
```

This proves:

> In an all-even graph, for every vertex `u`, there is a closed trail starting and ending at `u` that is maximal among trails starting at `u`.

Natural-language proof:

1. Use [`exists_maximalTrailFrom`](#simplegraphwalkexists_maximaltrailfrom) to get a maximal trail `p : G.Walk u v`.
2. Use [`MaximalTrailFrom.isClosed_of_forall_even_degree`](#simplegraphwalkmaximaltrailfromisclosed_of_forall_even_degree) to prove `u = v`.
3. Rewrite the endpoint and return `p` as a closed walk.

---

## Global maximal trail existence

### `SimpleGraph.Walk.trailLengthSetAll`

```lean
noncomputable def trailLengthSetAll : Finset ℕ
```

This finset contains all possible lengths of trails anywhere in the graph:

```lean
(Finset.range (G.edgeFinset.card + 1)).filter fun n =>
  ∃ x, ∃ y, ∃ p : G.Walk x y, p.IsTrail ∧ p.edges.length = n
```

This is the global analogue of `trailLengthSet`.

---

### `SimpleGraph.Walk.zero_mem_trailLengthSetAll`

```lean
theorem zero_mem_trailLengthSetAll (u : V) :
    0 ∈ (trailLengthSetAll (G := G) : Finset ℕ)
```

This proves that the global trail-length set is nonempty.

Natural-language proof:

1. Use the empty walk `nil : G.Walk u u`.
2. Its length is zero.
3. It is a trail.

This lemma is used to define `maxTrailLengthAll`.

---

### `SimpleGraph.Walk.maxTrailLengthAll`

```lean
noncomputable def maxTrailLengthAll (u : V) : ℕ
```

This is the maximum length of any trail anywhere in the graph.

The argument `u : V` is only used to provide a witness that `trailLengthSetAll` is nonempty through [`zero_mem_trailLengthSetAll`](#simplegraphwalkzero_mem_traillengthsetall).

---

### `SimpleGraph.Walk.trail_length_le_maxTrailLengthAll`

```lean
theorem trail_length_le_maxTrailLengthAll
    (u₀ : V)
    {x y : V} {p : G.Walk x y}
    (hp : p.IsTrail) :
    p.edges.length ≤ maxTrailLengthAll (G := G) u₀
```

This proves:

> Every trail in the graph has length at most the global maximum trail length.

Natural-language proof:

1. Show `p.edges.length ∈ trailLengthSetAll`.
2. Use [`IsTrail.length_edges_le_card_edgeFinset`](#simplegraphwalkistraillength_edges_le_card_edgefinset) for membership in the finite range.
3. Use the witnesses `x, y, p, hp, rfl`.
4. Apply `Finset.le_max'`.

This lemma is used by:

- [`exists_maximalTrail`](#simplegraphwalkexists_maximaltrail).

---

### `SimpleGraph.Walk.exists_maximalTrail`

```lean
theorem exists_maximalTrail
    (u₀ : V) :
    ∃ x, ∃ y, ∃ p : G.Walk x y, MaximalTrail p
```

This proves:

> There exists a globally maximal trail.

Natural-language proof:

1. Let `maxTrailLengthAll u₀` be the maximum trail length anywhere in the graph.
2. Since this maximum lies in `trailLengthSetAll`, unpack witnesses `x`, `y`, and `p : G.Walk x y`.
3. Show `p.IsTrail`.
4. For any trail `q`, use [`trail_length_le_maxTrailLengthAll`](#simplegraphwalktrail_length_le_maxtraillengthall).
5. Rewrite using the equality `p.edges.length = maxTrailLengthAll u₀`.
6. Conclude that `q` is no longer than `p`.

This lemma is used by:

- [`exists_closed_maximalTrail_of_forall_even_degree`](#simplegraphwalkexists_closed_maximaltrail_of_forall_even_degree).

---

### `SimpleGraph.Walk.exists_closed_maximalTrail_of_forall_even_degree`

```lean
theorem exists_closed_maximalTrail_of_forall_even_degree
    (u₀ : V)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    ∃ u, ∃ p : G.Walk u u, MaximalTrail p
```

This proves:

> In an all-even graph, there exists a closed globally maximal trail.

Natural-language proof:

1. Use [`exists_maximalTrail`](#simplegraphwalkexists_maximaltrail) to get a globally maximal trail `p : G.Walk x y`.
2. Use [`MaximalTrail.isClosed_of_forall_even_degree`](#simplegraphwalkmaximaltrailisclosed_of_forall_even_degree) to show `x = y`.
3. Rewrite and return `p` as a closed trail.

This lemma is used directly in the final theorem.

---

## Connectedness and unused incident edges

### `SimpleGraph.Walk.exists_unused_incident_edge_of_walk_to_not_support`

```lean
theorem exists_unused_incident_edge_of_walk_to_not_support
    {u v x y : V} {p : G.Walk u v}
    (w : G.Walk x y)
    (hx : x ∈ p.support)
    (hy : y ∉ p.support) :
    ∃ a b : V, a ∈ p.support ∧ G.Adj a b ∧ s(a, b) ∉ p.edges
```

This lemma proves:

> If a walk `w` starts at a vertex in `p.support` and ends at a vertex not in `p.support`, then along `w` there is a first edge leaving `p.support`. That edge is incident to `p.support` and is unused by `p`.

Natural-language proof:

The proof is by induction on `w`.

#### Base case

If `w = nil`, then its start and endpoint are the same vertex.
This contradicts the assumptions:

- `hx : x ∈ p.support`;
- `hy : x ∉ p.support`.

#### Inductive step

Suppose `w = cons hab tail`.

The edge `hab` goes from the current start vertex to the next vertex, which Lean accesses as `tail.getVert 0`.

There are two cases.

##### Case 1: the next vertex is in `p.support`

Then the first edge has not yet left `p.support`. Apply the induction hypothesis to `tail`.

##### Case 2: the next vertex is not in `p.support`

Then the first edge itself leaves `p.support`.

Take this edge as the witness:

- the first endpoint is in `p.support` by `hx`;
- the adjacency is `hab`;
- the edge cannot be in `p.edges`, because if it were, then [`SimpleGraph.Walk.mem_support_of_mem_edges`](#simplegraphwalkmem_support_of_mem_edges) would imply that the second endpoint is also in `p.support`, contradicting the case assumption.

This lemma is used by:

- [`MaximalTrail.isEulerian_of_connected`](#simplegraphwalkmaximaltrailiseulerian_of_connected).

---

## Closed globally maximal trails are Eulerian in connected graphs

### `SimpleGraph.Walk.MaximalTrail.isEulerian_of_connected`

```lean
theorem MaximalTrail.isEulerian_of_connected
    {u : V} {p : G.Walk u u}
    (hpmax : MaximalTrail p)
    (hconn : G.Connected) :
    p.IsEulerian
```

This is the central maximal-trail theorem.

It proves:

> If `p` is a closed globally maximal trail in a connected graph, then `p` is Eulerian.

The proof uses Mathlib’s Eulerian constructor:

```lean
SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem
```

This reduces the goal to:

```lean
∀ e ∈ G.edgeSet, e ∈ p.edges
```

So the proof assumes that some graph edge `e` is not in `p.edges` and derives a contradiction.

Natural-language proof:

1. Since `hpmax : MaximalTrail p`, `p` is a trail.
2. To prove `p.IsEulerian`, it suffices to show that every edge of `G` lies in `p.edges`.
3. Suppose some edge `e ∈ G.edgeSet` is not in `p.edges`.
4. Write `e = s(a, b)` and get `G.Adj a b`.
5. If `a ∈ p.support`, then the unused edge `s(a, b)` is incident to the support of `p`.
6. If `b ∈ p.support`, then the unused edge `s(b, a)` is incident to the support of `p`.
7. If neither endpoint is in `p.support`, use connectedness:
   - since `G` is connected, `G.Reachable u a`;
   - unpack this as a walk `w : G.Walk u a`;
   - `u ∈ p.support` because `p` is a walk from `u` to `u`;
   - `a ∉ p.support` by assumption;
   - apply [`exists_unused_incident_edge_of_walk_to_not_support`](#simplegraphwalkexists_unused_incident_edge_of_walk_to_not_support).
8. Thus in all cases there is an unused edge `s(x, y)` with:
   - `x ∈ p.support`;
   - `G.Adj x y`;
   - `s(x, y) ∉ p.edges`.

Now use closedness and maximality:

9. Since `p` is closed and `x ∈ p.support`, rotate `p` to start and end at `x`:
   ```lean
   let q : G.Walk x x := p.rotate x hxp
   ```
10. By `SimpleGraph.Walk.isTrail_rotate`, `q` is a trail.
11. By `SimpleGraph.Walk.rotate_edges`, the rotated walk has the same edge membership as `p`, so `s(x, y) ∉ q.edges`.
12. Prepend the unused edge `y -- x` to `q`.
13. By [`IsTrail.exists_longer_of_unused_edge_at_start`](#simplegraphwalkistrail.exists_longer_of_unused_edge_at_start), this gives a trail `r : G.Walk y x` with:
   ```lean
   q.edges.length < r.edges.length
   ```
14. By `SimpleGraph.Walk.rotate_edges`, rotation preserves edge-list length:
   ```lean
   q.edges.length = p.edges.length
   ```
15. Therefore:
   ```lean
   p.edges.length < r.edges.length
   ```
16. But `hpmax` says no trail is longer than `p`, contradiction.
17. Hence no graph edge is missing from `p.edges`.
18. Therefore `p.IsEulerian`.

Important Lean ingredients:

- `SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem`;
- [`exists_unused_incident_edge_of_walk_to_not_support`](#simplegraphwalkexists_unused_incident_edge_of_walk_to_not_support);
- `SimpleGraph.Walk.rotate`;
- `SimpleGraph.Walk.isTrail_rotate`;
- `SimpleGraph.Walk.rotate_edges`;
- [`IsTrail.exists_longer_of_unused_edge_at_start`](#simplegraphwalkistrail.exists_longer_of_unused_edge_at_start);
- `SimpleGraph.Connected.preconnected`, accessed in the proof as:
  ```lean
  hconn.1 u a
  ```

---

## Overall dependency graph

The main theorem depends on the following chain:

```text
exists_isEulerian_of_connected_forall_even_degree
├─ exists_closed_maximalTrail_of_forall_even_degree
│  ├─ exists_maximalTrail
│  │  ├─ trail_length_le_maxTrailLengthAll
│  │  │  └─ IsTrail.length_edges_le_card_edgeFinset
│  │  └─ zero_mem_trailLengthSetAll
│  └─ MaximalTrail.isClosed_of_forall_even_degree
│     ├─ MaximalTrail.toMaximalTrailFrom
│     └─ MaximalTrailFrom.isClosed_of_forall_even_degree
│        ├─ IsTrail.odd_countP_edges_right_of_ne
│        │  └─ IsTrail.not_even_countP_edges_right_of_ne
│        └─ MaximalTrailFrom.countP_edges_right_eq_degree
│           └─ MaximalTrailFrom.filter_edgesFinset_eq_incidenceFinset
│              ├─ exists_adj_of_mem_edgeSet_and_mem
│              └─ MaximalTrailFrom.not_unused_edge_at_end
│                 └─ IsTrail.exists_longer_of_unused_edge_at_start
│                    └─ IsTrail.cons_of_unused_edge
└─ MaximalTrail.isEulerian_of_connected
   ├─ exists_unused_incident_edge_of_walk_to_not_support
   ├─ IsTrail.exists_longer_of_unused_edge_at_start
   └─ SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem
```

---

## Notes for moving this into Mathlib

The current proof is correct structurally, but the public API should probably be minimized before opening a PR.

Likely candidates to keep public:

```lean
theorem exists_isEulerian_of_connected_forall_even_degree
```

Possibly useful public helper lemmas:

```lean
theorem IsTrail.length_edges_le_card_edgeFinset
theorem MaximalTrail.isEulerian_of_connected
```

Likely candidates to make private or local to the proof:

```lean
MaximalTrailFrom
MaximalTrail
trailLengthSet
trailLengthSetAll
maxTrailLengthFrom
maxTrailLengthAll
exists_unused_incident_edge_of_walk_to_not_support
```

If reviewers want a cleaner public interface, the maximal-trail predicates can be kept private and the final theorem can remain the main exported statement.

---

## Glossary of key Lean names

| Lean name | Meaning |
|---|---|
| `p.IsTrail` | `p` has no repeated edges |
| `p.IsEulerian` | `p` is an Eulerian walk |
| `p.edges` | list of edges traversed by `p` |
| `p.support` | list of vertices visited by `p` |
| `G.edgeSet` | set of graph edges |
| `G.edgeFinset` | finite set of graph edges |
| `G.incidenceFinset v` | finite set of graph edges incident to `v` |
| `G.degree v` | degree of vertex `v` |
| `G.Connected` | `G` is preconnected and nonempty |
| `G.Reachable u v` | there exists a walk from `u` to `v` |
| `p.rotate x hxp` | closed walk `p` rotated to start and end at `x` |
| `p.rotate_edges x hxp` | rotated closed walk has edge list cyclically related to `p.edges` |
