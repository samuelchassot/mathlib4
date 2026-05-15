import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

open scoped Sym2

namespace SimpleGraph
namespace Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

#check SimpleGraph.Walk.IsEulerian
#check SimpleGraph.Walk.IsTrail
#check SimpleGraph.Walk.IsEulerian.isTrail
#check SimpleGraph.Walk.IsEulerian.even_degree_iff
#check SimpleGraph.Walk.IsEulerian.card_odd_degree

#check SimpleGraph.Connected
#check SimpleGraph.Preconnected

#check SimpleGraph.Walk.nil
#check SimpleGraph.Walk.cons
#check SimpleGraph.Walk.append
#check SimpleGraph.Walk.reverse
#check SimpleGraph.Walk.edges
#check SimpleGraph.Walk.support

#check SimpleGraph.Walk.IsTrail
#check SimpleGraph.Walk.IsTrail.cons
#check SimpleGraph.Walk.IsTrail.reverse

#check SimpleGraph.Walk.edges_reverse
#check List.length_reverse
#check List.mem_reverse

#check SimpleGraph.card_incidenceFinset_eq_degree
#check SimpleGraph.incidenceFinset_eq_filter
#check SimpleGraph.Walk.IsTrail.edgesFinset
#check SimpleGraph.Walk.edges_subset_edgeSet
#check SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem
#check SimpleGraph.Walk.IsTrail.even_countP_edges_iff
#check SimpleGraph.Walk.IsTrail.edges_nodup
#check Multiset.countP_eq_card_filter
#check Multiset.coe_countP

#check SimpleGraph.incidenceFinset
#check SimpleGraph.mem_incidenceFinset
#check SimpleGraph.incidenceSet
#check SimpleGraph.mem_incidenceSet
#check SimpleGraph.edgeSet
#check SimpleGraph.mem_edgeSet
#check Sym2.mem_iff
#check Sym2.eq_swap

#check List.toFinset_card_of_nodup
#check Finset.card_le_card
#check List.mem_toFinset
#check SimpleGraph.edgeFinset


#check SimpleGraph.Connected
#check SimpleGraph.Preconnected
#check SimpleGraph.Reachable
#check SimpleGraph.Walk.IsPath
#check SimpleGraph.Walk.toPath
#check SimpleGraph.Walk.support
#check SimpleGraph.Walk.edges_subset_edgeSet
#check SimpleGraph.Walk.isTrail_def
#check SimpleGraph.Walk.getVert
#check SimpleGraph.Walk.start_mem_support
#check SimpleGraph.Walk.end_mem_support
#check SimpleGraph.Walk.mem_support_iff
#check SimpleGraph.Walk.mem_support_iff_exists_append
#check SimpleGraph.Walk.mem_support_iff_exists_mem_edges
#check SimpleGraph.Walk.mem_support_of_mem_edges
#check SimpleGraph.Walk.fst_mem_support_of_mem_edges
#check SimpleGraph.Walk.snd_mem_support_of_mem_edges
#check SimpleGraph.Walk.rotate
#check SimpleGraph.Walk.isTrail_rotate
#check SimpleGraph.Walk.mem_support_rotate_iff

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem IsTrail.cons_of_unused_edge
    {u v w : V} {p : G.Walk v w}
    (hp : p.IsTrail)
    (huv : G.Adj u v)
    (hunused : s(u, v) ∉ p.edges) :
    (SimpleGraph.Walk.cons huv p).IsTrail := by
  exact hp.cons huv hunused

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem IsTrail.exists_longer_of_unused_edge_at_start
    {u v w : V} {p : G.Walk v w}
    (hp : p.IsTrail)
    (huv : G.Adj u v)
    (hunused : s(u, v) ∉ p.edges) :
    ∃ q : G.Walk u w, q.IsTrail ∧ p.edges.length < q.edges.length := by
  refine ⟨SimpleGraph.Walk.cons huv p, ?_, ?_⟩
  · exact hp.cons huv hunused
  · simp


-- Maximal trails
omit [DecidableEq V] [DecidableRel G.Adj] in
def MaximalTrailFrom {u v : V} (p : G.Walk u v) : Prop :=
  p.IsTrail ∧
    ∀ ⦃w : V⦄ (q : G.Walk u w),
      q.IsTrail →
      q.edges.length ≤ p.edges.length

omit [DecidableEq V] [DecidableRel G.Adj] in
def MaximalTrail {u v : V} (p : G.Walk u v) : Prop :=
  p.IsTrail ∧
    ∀ ⦃x y : V⦄ (q : G.Walk x y),
      q.IsTrail →
      q.edges.length ≤ p.edges.length

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem MaximalTrail.toMaximalTrailFrom
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p) :
    MaximalTrailFrom p := by
  constructor
  · exact hpmax.1
  · intro w q hq
    exact hpmax.2 q hq


-- endpoint/maximality lemmas
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem MaximalTrailFrom.not_unused_edge_at_end
    {u v w : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p)
    (hvw : G.Adj v w) :
    s(v, w) ∈ p.edges := by
  by_contra hunused

  have hpTrail : p.IsTrail := hpmax.1
  have hpRevTrail : p.reverse.IsTrail :=
    SimpleGraph.Walk.IsTrail.reverse p hpTrail

  have hunusedRev : s(w, v) ∉ p.reverse.edges := by
    intro hmem
    apply hunused
    rw [SimpleGraph.Walk.edges_reverse] at hmem
    have hmem' : s(w, v) ∈ p.edges := by
      exact (List.mem_reverse).mp hmem
    simpa [Sym2.eq_swap] using hmem'

  obtain ⟨q, hqTrail, hqLen⟩ :
      ∃ q : G.Walk w u, q.IsTrail ∧ p.reverse.edges.length < q.edges.length :=
    IsTrail.exists_longer_of_unused_edge_at_start
      (p := p.reverse) hpRevTrail hvw.symm hunusedRev

  have hqRevTrail : q.reverse.IsTrail :=
    SimpleGraph.Walk.IsTrail.reverse q hqTrail

  have hmax := hpmax.2 q.reverse hqRevTrail

  have hpLenRev : p.reverse.edges.length = p.edges.length := by
    rw [SimpleGraph.Walk.edges_reverse, List.length_reverse]

  have hqLenRev : q.reverse.edges.length = q.edges.length := by
    rw [SimpleGraph.Walk.edges_reverse, List.length_reverse]

  have hqLong' : p.edges.length < q.reverse.edges.length := by
    omega

  exact Nat.not_lt_of_ge hmax hqLong'


omit [Fintype V] [DecidableRel G.Adj] in
theorem IsTrail.not_even_countP_edges_right_of_ne
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (huv : u ≠ v) :
    ¬ Even (p.edges.countP fun e => v ∈ e) := by
  intro hEven
  have h := (hp.even_countP_edges_iff v).mp hEven
  exact (h huv).2 rfl

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsTrail.odd_countP_edges_right_of_ne
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (huv : u ≠ v) :
    Odd (p.edges.countP fun e => v ∈ e) := by
  rw [← Nat.not_even_iff_odd]
  exact hp.not_even_countP_edges_right_of_ne huv


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_adj_of_mem_edgeSet_and_mem
    {v : V} {e : Sym2 V}
    (heG : e ∈ G.edgeSet)
    (hev : v ∈ e) :
    ∃ w, G.Adj v w ∧ e = s(v, w) := by
  induction e using Sym2.ind with
  | h a b =>
      rw [Sym2.mem_iff] at hev
      have hab : G.Adj a b := (G.mem_edgeSet).mp heG
      rcases hev with rfl | rfl
      · exact ⟨b, hab, rfl⟩
      · refine ⟨a, hab.symm, ?_⟩
        exact Sym2.eq_swap


theorem MaximalTrailFrom.filter_edgesFinset_eq_incidenceFinset
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p) :
    hpmax.1.edgesFinset.filter (fun e => v ∈ e) = G.incidenceFinset v := by
  ext e
  constructor
  · intro he
    rw [Finset.mem_filter] at he
    rw [G.incidenceFinset_eq_filter v]
    rw [Finset.mem_filter]
    constructor
    · have hep : e ∈ p.edges := by
        simpa [IsTrail.edgesFinset] using he.1
      have heG : e ∈ G.edgeSet := p.edges_subset_edgeSet hep
      simpa using heG
    · exact he.2
  · intro he
    have he' : e ∈ G.edgeSet ∧ v ∈ e := by
      rw [G.incidenceFinset_eq_filter v] at he
      simpa using he
    rcases exists_adj_of_mem_edgeSet_and_mem (G := G) he'.1 he'.2 with ⟨w, hvw, rfl⟩
    rw [Finset.mem_filter]
    constructor
    · simpa [IsTrail.edgesFinset] using hpmax.not_unused_edge_at_end hvw
    · simp

theorem MaximalTrailFrom.countP_edges_right_eq_degree
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p) :
    p.edges.countP (fun e => v ∈ e) =
      @SimpleGraph.degree V G v
        (Subtype.fintype (Membership.mem (G.neighborSet v))) := by
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
  rw [← SimpleGraph.card_incidenceFinset_eq_degree G v]
  change (hpmax.1.edgesFinset.filter (fun e => v ∈ e)).card =
    (G.incidenceFinset v).card
  rw [hpmax.filter_edgesFinset_eq_incidenceFinset]

theorem MaximalTrailFrom.isClosed_of_forall_even_degree
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p)
    (heven : ∀ x : V,
      Even (@SimpleGraph.degree V G x
        (Subtype.fintype (Membership.mem (G.neighborSet x))))) :
    u = v := by
  by_contra huv

  have hOddCount : Odd (p.edges.countP fun e => v ∈ e) :=
    hpmax.1.odd_countP_edges_right_of_ne huv

  have hCountDegree :
      p.edges.countP (fun e => v ∈ e) =
        @SimpleGraph.degree V G v
          (Subtype.fintype (Membership.mem (G.neighborSet v))) :=
    hpmax.countP_edges_right_eq_degree

  have hOddDegree :
      Odd (@SimpleGraph.degree V G v
        (Subtype.fintype (Membership.mem (G.neighborSet v)))) := by
    simpa [hCountDegree] using hOddCount

  exact (Nat.not_even_iff_odd.mpr hOddDegree) (heven v)


noncomputable def trailLengthSet (u : V) : Finset ℕ := by classical
  exact (Finset.range (G.edgeFinset.card + 1)).filter fun n =>
    ∃ v, ∃ p : G.Walk u v, p.IsTrail ∧ p.edges.length = n

theorem zero_mem_trailLengthSet (u : V) :
    0 ∈ trailLengthSet (G := G) u := by
  unfold trailLengthSet
  simp
  exact ⟨u, SimpleGraph.Walk.nil, by simp, by simp⟩


-- length bound
theorem IsTrail.length_edges_le_card_edgeFinset
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) :
    p.edges.length ≤ G.edgeFinset.card := by
  have hsub : p.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    rw [List.mem_toFinset] at he
    have heG : e ∈ G.edgeSet := p.edges_subset_edgeSet he
    simpa using heG
  have hnodup : p.edges.Nodup := hp.edges_nodup
  rw [← List.toFinset_card_of_nodup hnodup]
  exact Finset.card_le_card hsub

-- global maximality
noncomputable def trailLengthSetAll : Finset ℕ := by
  classical
  exact (Finset.range (G.edgeFinset.card + 1)).filter fun n =>
    ∃ x, ∃ y, ∃ p : G.Walk x y, p.IsTrail ∧ p.edges.length = n

theorem zero_mem_trailLengthSetAll (u : V) :
    0 ∈ (trailLengthSetAll (G := G) : Finset ℕ) := by
  classical
  unfold trailLengthSetAll
  simp
  exact ⟨u, u, SimpleGraph.Walk.nil, by simp, by simp⟩

noncomputable def maxTrailLengthAll (u : V) : ℕ :=
  (trailLengthSetAll (G := G)).max'
    ⟨0, zero_mem_trailLengthSetAll (G := G) u⟩

theorem trail_length_le_maxTrailLengthAll
    (u₀ : V)
    {x y : V} {p : G.Walk x y}
    (hp : p.IsTrail) :
    p.edges.length ≤ maxTrailLengthAll (G := G) u₀ := by
  classical
  unfold maxTrailLengthAll
  apply Finset.le_max'
  unfold trailLengthSetAll
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_range]
    exact Nat.lt_succ_of_le hp.length_edges_le_card_edgeFinset
  · exact ⟨x, y, p, hp, rfl⟩

theorem exists_maximalTrail
    (u₀ : V) :
    ∃ x, ∃ y, ∃ p : G.Walk x y, MaximalTrail p := by
  classical

  have hmax_mem :
      maxTrailLengthAll (G := G) u₀ ∈ trailLengthSetAll (G := G) := by
    unfold maxTrailLengthAll
    exact Finset.max'_mem _ _

  unfold trailLengthSetAll at hmax_mem
  rw [Finset.mem_filter] at hmax_mem
  rcases hmax_mem.2 with ⟨x, y, p, hpTrail, hpLen⟩

  refine ⟨x, y, p, ?_⟩
  constructor
  · exact hpTrail
  · intro a b q hqTrail
    have hqLe := trail_length_le_maxTrailLengthAll (G := G) u₀ hqTrail
    rw [hpLen]
    exact hqLe

theorem MaximalTrail.isClosed_of_forall_even_degree
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p)
    (heven : ∀ x : V,
      Even (@SimpleGraph.degree V G x
        (Subtype.fintype (Membership.mem (G.neighborSet x))))) :
    u = v := by
  exact hpmax.toMaximalTrailFrom.isClosed_of_forall_even_degree heven


theorem exists_closed_maximalTrail_of_forall_even_degree
    (u₀ : V)
    (heven : ∀ x : V,
      Even (@SimpleGraph.degree V G x
        (Subtype.fintype (Membership.mem (G.neighborSet x))))) :
    ∃ u, ∃ p : G.Walk u u, MaximalTrail p := by
  obtain ⟨x, y, p, hpmax⟩ := exists_maximalTrail (G := G) u₀
  have hxy : x = y := hpmax.isClosed_of_forall_even_degree heven
  subst y
  exact ⟨x, p, hpmax⟩


noncomputable def maxTrailLengthFrom (u : V) : ℕ :=
  (trailLengthSet (G := G) u).max'
    ⟨0, zero_mem_trailLengthSet (G := G) u⟩

theorem trail_length_le_maxTrailLengthFrom
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) :
    p.edges.length ≤ maxTrailLengthFrom (G := G) u := by classical
  unfold maxTrailLengthFrom
  apply Finset.le_max'
  unfold trailLengthSet
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_range]
    exact Nat.lt_succ_of_le hp.length_edges_le_card_edgeFinset
  · exact ⟨v, p, hp, rfl⟩

theorem exists_maximalTrailFrom
    (u : V) :
    ∃ v, ∃ p : G.Walk u v, MaximalTrailFrom p := by
  classical

  have hmax_mem :
      maxTrailLengthFrom (G := G) u ∈ trailLengthSet (G := G) u := by
    unfold maxTrailLengthFrom
    exact Finset.max'_mem _ _

  unfold trailLengthSet at hmax_mem
  rw [Finset.mem_filter] at hmax_mem
  rcases hmax_mem.2 with ⟨v, p, hpTrail, hpLen⟩

  refine ⟨v, p, ?_⟩
  constructor
  · exact hpTrail
  · intro w q hqTrail
    have hqLe := trail_length_le_maxTrailLengthFrom (G := G) hqTrail
    rw [hpLen]
    exact hqLe

theorem exists_closed_maximalTrailFrom_of_forall_even_degree
    (u : V)
    (heven : ∀ x : V,
      Even (@SimpleGraph.degree V G x
        (Subtype.fintype (Membership.mem (G.neighborSet x))))) :
    ∃ p : G.Walk u u, MaximalTrailFrom p := by
  obtain ⟨v, p, hpmax⟩ := exists_maximalTrailFrom (G := G) u
  have huv : u = v := hpmax.isClosed_of_forall_even_degree heven
  subst v
  exact ⟨p, hpmax⟩


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_unused_incident_edge_of_walk_to_not_support
    {u v x y : V} {p : G.Walk u v}
    (w : G.Walk x y)
    (hx : x ∈ p.support)
    (hy : y ∉ p.support) :
    ∃ a b : V, a ∈ p.support ∧ G.Adj a b ∧ s(a, b) ∉ p.edges := by
  induction w with
  | nil =>
      exact (hy hx).elim
  | cons hab tail ih =>
      by_cases hb : tail.getVert 0 ∈ p.support
      · exact ih (by simpa using hb) hy
      · refine ⟨_, _, hx, hab, ?_⟩
        intro hedge
        exact hb (p.mem_support_of_mem_edges hedge (by simp [Sym2.mem_iff]))


omit [Fintype V] [DecidableRel G.Adj] in
theorem MaximalTrail.isEulerian_of_connected
    {u : V} {p : G.Walk u u}
    (hpmax : MaximalTrail p)
    (hconn : G.Connected) :
    p.IsEulerian := by
  refine hpmax.1.isEulerian_of_forall_mem ?_
  intro e he
  by_contra hnot

  suffices ∃ x y : V, x ∈ p.support ∧ G.Adj x y ∧ s(x, y) ∉ p.edges by
    rcases this with ⟨x, y, hxp, hxy, hxy_not⟩

    let q : G.Walk x x := p.rotate x hxp

    have hqTrail : q.IsTrail := by
      dsimp [q]
      simpa using (SimpleGraph.Walk.isTrail_rotate (c := p) hxp).mpr hpmax.1

    have hxy_not_q : s(x, y) ∉ q.edges := by
      intro hmem
      apply hxy_not
      dsimp [q] at hmem
      exact ((p.rotate_edges x hxp).mem_iff).mp hmem

    obtain ⟨r, hrTrail, hrLen⟩ :
        ∃ r : G.Walk y x, r.IsTrail ∧ q.edges.length < r.edges.length :=
      IsTrail.exists_longer_of_unused_edge_at_start
        (p := q) hqTrail hxy.symm (by
          simpa [Sym2.eq_swap] using hxy_not_q)

    have hmax := hpmax.2 r hrTrail

    have hqLen : q.edges.length = p.edges.length := by
      dsimp [q]
      exact (p.rotate_edges x hxp).perm.length_eq

    have : p.edges.length < r.edges.length := by
      omega

    exact Nat.not_lt_of_ge hmax this

  induction e using Sym2.ind with
  | h a b =>
      have hab : G.Adj a b := (G.mem_edgeSet).mp he

      by_cases ha : a ∈ p.support
      · exact ⟨a, b, ha, hab, by simpa using hnot⟩

      by_cases hb : b ∈ p.support
      · refine ⟨b, a, hb, hab.symm, ?_⟩
        intro hba
        apply hnot
        simpa [Sym2.eq_swap] using hba

      have hreach : G.Reachable u a := by
        exact hconn.1 u a

      rcases hreach with ⟨w⟩

      exact exists_unused_incident_edge_of_walk_to_not_support
        (p := p) w p.start_mem_support ha


theorem exists_isEulerian_of_connected_forall_even_degree
    (u₀ : V)
    (hconn : G.Connected)
    (heven : ∀ x : V,
      Even (@SimpleGraph.degree V G x
        (Subtype.fintype (Membership.mem (G.neighborSet x))))) :
    ∃ u, ∃ p : G.Walk u u, p.IsEulerian := by
  obtain ⟨u, p, hpmax⟩ :=
    exists_closed_maximalTrail_of_forall_even_degree (G := G) u₀ heven
  exact ⟨u, p, hpmax.isEulerian_of_connected hconn⟩

#print SimpleGraph.Connected
#print SimpleGraph.Preconnected


example {u v : V} (p : G.Walk u v) (h : p.IsEulerian) :
    p.IsTrail := by
  exact h.isTrail

example {u : V} {p : G.Walk u u} (h : p.IsEulerian) (x : V) :
    Even (@SimpleGraph.degree V G x
      (Subtype.fintype (Membership.mem (G.neighborSet x)))) := by
  exact (h.even_degree_iff (x := x)).mpr (by
    intro huu
    exact False.elim (huu rfl))

end Walk
end SimpleGraph
