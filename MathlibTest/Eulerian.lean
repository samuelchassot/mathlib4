import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

open scoped Sym2

namespace SimpleGraph
namespace Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem IsTrail.cons_of_unused_edge
    {u v w : V} {p : G.Walk v w}
    (hp : p.IsTrail)
    (huv : G.Adj u v)
    (hunused : s(u, v) ∉ p.edges) :
    (SimpleGraph.Walk.cons huv p).IsTrail := by
  exact hp.cons huv hunused

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem IsTrail.exists_longer_of_unused_edge_at_start
    {u v w : V} {p : G.Walk v w}
    (hp : p.IsTrail)
    (huv : G.Adj u v)
    (hunused : s(u, v) ∉ p.edges) :
    ∃ q : G.Walk u w, q.IsTrail ∧ p.edges.length < q.edges.length := by
  refine ⟨SimpleGraph.Walk.cons huv p, ?_, ?_⟩
  · exact hp.cons huv hunused
  · simp

omit [DecidableEq V] [DecidableRel G.Adj] in
private def MaximalTrailFrom {u v : V} (p : G.Walk u v) : Prop :=
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
private theorem MaximalTrail.to_MaximalTrailFrom
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p) :
    MaximalTrailFrom p := by
  constructor
  · exact hpmax.1
  · intro w q hq
    exact hpmax.2 q hq


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem MaximalTrailFrom.not_unused_edge_at_end
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
private theorem IsTrail.not_even_countP_edges_right_of_ne
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (huv : u ≠ v) :
    ¬ Even (p.edges.countP fun e => v ∈ e) := by
  intro hEven
  have h := (hp.even_countP_edges_iff v).mp hEven
  exact (h huv).2 rfl

omit [Fintype V] [DecidableRel G.Adj] in
private theorem IsTrail.odd_countP_edges_right_of_ne
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (huv : u ≠ v) :
    Odd (p.edges.countP fun e => v ∈ e) := by
  rw [← Nat.not_even_iff_odd]
  exact hp.not_even_countP_edges_right_of_ne huv


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem exists_adj_of_mem_edgeSet_and_mem
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


private theorem MaximalTrailFrom.filter_edgesFinset_eq_incidenceFinset
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

private theorem MaximalTrailFrom.countP_edges_right_eq_degree
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

private theorem MaximalTrailFrom.is_closed_of_forall_even_degree
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p)
    (heven : ∀ x : V,
      Even (G.degree x)) :
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

omit [DecidableEq V] in
private theorem zero_mem_trailLengthSet (u : V) :
  0 ∈ trailLengthSet (G := G) u := by
  unfold trailLengthSet
  simp
  exact ⟨u, SimpleGraph.Walk.nil, by simp, by simp⟩


private theorem IsTrail.length_edges_le_card_edgeFinset
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

omit [DecidableEq V] [DecidableRel G.Adj] in
private def MaximalTrailAvoidingFrom
    {u v x y : V} (p : G.Walk u v) (q : G.Walk x y) : Prop :=
  q.IsTrail ∧
    q.edges.Disjoint p.edges ∧
    ∀ ⦃z : V⦄ (r : G.Walk x z),
      r.IsTrail →
      r.edges.Disjoint p.edges →
      r.edges.length ≤ q.edges.length


private noncomputable def trailLengthSetAvoidingFrom
    {u v : V} (p : G.Walk u v) (x : V) : Finset ℕ := by
  classical
  exact (Finset.range (G.edgeFinset.card + 1)).filter fun n =>
    ∃ y, ∃ q : G.Walk x y,
      q.IsTrail ∧ q.edges.Disjoint p.edges ∧ q.edges.length = n


omit [DecidableEq V] in
private theorem zero_mem_trailLengthSetAvoidingFrom
    {u v : V} (p : G.Walk u v) (x : V) :
    0 ∈ trailLengthSetAvoidingFrom (G := G) p x := by
  classical
  unfold trailLengthSetAvoidingFrom
  simp
  exact ⟨x, SimpleGraph.Walk.nil, by simp, by simp, by simp⟩


private noncomputable def maxTrailLengthAvoidingFrom
    {u v : V} (p : G.Walk u v) (x : V) : ℕ :=
  (trailLengthSetAvoidingFrom (G := G) p x).max'
    ⟨0, zero_mem_trailLengthSetAvoidingFrom (G := G) p x⟩


private theorem trail_length_le_maxTrailLengthAvoidingFrom
    {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hqTrail : q.IsTrail)
    (hqDisj : q.edges.Disjoint p.edges) :
    q.edges.length ≤ maxTrailLengthAvoidingFrom (G := G) p x := by
  classical
  unfold maxTrailLengthAvoidingFrom
  apply Finset.le_max'
  unfold trailLengthSetAvoidingFrom
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_range]
    exact Nat.lt_succ_of_le hqTrail.length_edges_le_card_edgeFinset
  · exact ⟨y, q, hqTrail, hqDisj, rfl⟩


private theorem exists_maximalTrailAvoidingFrom
    {u v : V} (p : G.Walk u v) (x : V) :
    ∃ y, ∃ q : G.Walk x y, MaximalTrailAvoidingFrom p q := by
  classical

  have hmax_mem :
      maxTrailLengthAvoidingFrom (G := G) p x ∈
        trailLengthSetAvoidingFrom (G := G) p x := by
    unfold maxTrailLengthAvoidingFrom
    exact Finset.max'_mem _ _

  unfold trailLengthSetAvoidingFrom at hmax_mem
  rw [Finset.mem_filter] at hmax_mem
  rcases hmax_mem.2 with ⟨y, q, hqTrail, hqDisj, hqLen⟩

  refine ⟨y, q, ?_⟩
  constructor
  · exact hqTrail
  constructor
  · exact hqDisj
  · intro z r hrTrail hrDisj
    have hrLe :
        r.edges.length ≤ maxTrailLengthAvoidingFrom (G := G) p x :=
      trail_length_le_maxTrailLengthAvoidingFrom
        (G := G) (p := p) (q := r) hrTrail hrDisj
    rw [hqLen]
    exact hrLe

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem MaximalTrailAvoidingFrom.not_unused_edge_at_end
    {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hqmax : MaximalTrailAvoidingFrom p q)
    (hyz : G.Adj y z)
    (hnotp : s(y, z) ∉ p.edges) :
    s(y, z) ∈ q.edges := by
  by_contra hnotq

  have hqTrail : q.IsTrail := hqmax.1
  have hqDisj : q.edges.Disjoint p.edges := hqmax.2.1
  have hqMax :
      ∀ ⦃z : V⦄ (r : G.Walk x z),
        r.IsTrail →
        r.edges.Disjoint p.edges →
        r.edges.length ≤ q.edges.length := hqmax.2.2

  have hqRevTrail : q.reverse.IsTrail :=
    SimpleGraph.Walk.IsTrail.reverse q hqTrail

  have hnotqRev : s(z, y) ∉ q.reverse.edges := by
    intro hmem
    apply hnotq
    rw [SimpleGraph.Walk.edges_reverse] at hmem
    have hmem' : s(z, y) ∈ q.edges := by
      exact (List.mem_reverse).mp hmem
    simpa [Sym2.eq_swap] using hmem'

  let r : G.Walk x z := (SimpleGraph.Walk.cons hyz.symm q.reverse).reverse

  have hrTrail : r.IsTrail := by
    dsimp [r]
    apply SimpleGraph.Walk.IsTrail.reverse
    exact hqRevTrail.cons hyz.symm hnotqRev

  have hrDisj : r.edges.Disjoint p.edges := by
    intro e her hep
    dsimp [r] at her
    rw [SimpleGraph.Walk.edges_reverse] at her
    have her' : e ∈ (SimpleGraph.Walk.cons hyz.symm q.reverse).edges := by
      exact (List.mem_reverse).mp her
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at her'
    rcases her' with her_edge | her_qrev
    · subst her_edge
      exact hnotp (by simpa [Sym2.eq_swap] using hep)
    · have her_q : e ∈ q.edges := by
        rw [SimpleGraph.Walk.edges_reverse] at her_qrev
        exact (List.mem_reverse).mp her_qrev
      exact hqDisj her_q hep

  have hmax := hqMax r hrTrail hrDisj

  have hrLen : r.edges.length = q.edges.length + 1 := by
    dsimp [r]
    rw [SimpleGraph.Walk.edges_reverse, List.length_reverse]
    simp [SimpleGraph.Walk.edges_reverse, List.length_reverse]

  have hlong : q.edges.length < r.edges.length := by
    omega

  exact Nat.not_lt_of_ge hmax hlong

noncomputable def trailLengthSetAll : Finset ℕ := by
  classical
  exact (Finset.range (G.edgeFinset.card + 1)).filter fun n =>
    ∃ x, ∃ y, ∃ p : G.Walk x y, p.IsTrail ∧ p.edges.length = n

omit [DecidableEq V] in
private theorem zero_mem_trailLengthSetAll (u : V) :
    0 ∈ (trailLengthSetAll (G := G) : Finset ℕ) := by
  classical
  unfold trailLengthSetAll
  simp
  exact ⟨u, u, SimpleGraph.Walk.nil, by simp, by simp⟩

noncomputable def maxTrailLengthAll (u : V) : ℕ :=
  (trailLengthSetAll (G := G)).max'
    ⟨0, zero_mem_trailLengthSetAll (G := G) u⟩

private theorem trail_length_le_maxTrailLengthAll
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

private theorem exists_maximalTrail
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

private theorem MaximalTrail.is_closed_of_forall_even_degree
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    u = v := by
  exact hpmax.to_MaximalTrailFrom.is_closed_of_forall_even_degree heven


private theorem exists_closed_maximalTrail_of_forall_even_degree
    (u₀ : V)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    ∃ u, ∃ p : G.Walk u u, MaximalTrail p := by
  obtain ⟨x, y, p, hpmax⟩ := exists_maximalTrail (G := G) u₀
  have hxy : x = y := hpmax.is_closed_of_forall_even_degree heven
  subst y
  exact ⟨x, p, hpmax⟩


noncomputable def maxTrailLengthFrom (u : V) : ℕ :=
  (trailLengthSet (G := G) u).max'
    ⟨0, zero_mem_trailLengthSet (G := G) u⟩

private theorem trail_length_le_maxTrailLengthFrom
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

private theorem exists_maximalTrailFrom
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

private theorem exists_closed_maximalTrailFrom_of_forall_even_degree
    (u : V)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    ∃ p : G.Walk u u, MaximalTrailFrom p := by
  obtain ⟨v, p, hpmax⟩ := exists_maximalTrailFrom (G := G) u
  have huv : u = v := hpmax.is_closed_of_forall_even_degree heven
  subst v
  exact ⟨p, hpmax⟩


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem exists_unused_incident_edge_of_walk_to_not_support
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





private theorem even_degree_of_not_endpoint_of_card_odd_degree_eq_two
    {u v x : V}
    (huv : u ≠ v)
    (huOdd : Odd (G.degree u))
    (hvOdd : Odd (G.degree v))
    (hodd : Fintype.card {x : V | Odd (G.degree x)} = 2)
    (hxu : x ≠ u)
    (hxv : x ≠ v) :
    Even (G.degree x) := by
  classical
  by_contra hxEven

  have hxOdd : Odd (G.degree x) :=
    Nat.not_even_iff_odd.mp hxEven

  let U : {x : V | Odd (G.degree x)} := ⟨u, huOdd⟩
  let Vv : {x : V | Odd (G.degree x)} := ⟨v, hvOdd⟩
  let X : {x : V | Odd (G.degree x)} := ⟨x, hxOdd⟩

  have hUV : U ≠ Vv := by
    intro h
    exact huv (congrArg Subtype.val h)

  have hUX : U ≠ X := by
    intro h
    exact hxu (congrArg Subtype.val h).symm

  have hVX : Vv ≠ X := by
    intro h
    exact hxv (congrArg Subtype.val h).symm

  let t : Finset {x : V | Odd (G.degree x)} := insert U {Vv}

  have hU_not_singleton : U ∉ ({Vv} : Finset {x : V | Odd (G.degree x)}) := by
    intro h
    exact hUV (Finset.mem_singleton.mp h)

  have ht_card : t.card = 2 := by
    calc
      t.card = (insert U ({Vv} : Finset {x : V | Odd (G.degree x)})).card := rfl
      _ = ({Vv} : Finset {x : V | Odd (G.degree x)}).card + 1 :=
          Finset.card_insert_of_notMem hU_not_singleton
      _ = 1 + 1 := by rw [Finset.card_singleton]
      _ = 2 := by norm_num

  have hXnot : X ∉ t := by
    intro h
    have hmem := Finset.mem_insert.mp h
    rcases hmem with hXU | hXVv
    · exact hUX hXU.symm
    · have hXV : X = Vv := Finset.mem_singleton.mp hXVv
      exact hVX hXV.symm

  let s : Finset {x : V | Odd (G.degree x)} := insert X t

  have hs_card : s.card = 3 := by
    calc
      s.card = (insert X t).card := rfl
      _ = t.card + 1 := Finset.card_insert_of_notMem hXnot
      _ = 2 + 1 := by rw [ht_card]
      _ = 3 := by norm_num

  have hs_le_univ :
      s.card ≤ (Finset.univ : Finset {x : V | Odd (G.degree x)}).card :=
    Finset.card_le_card (by
      intro y hy
      exact Finset.mem_univ y)

  have hthree :
      3 ≤ Fintype.card {x : V | Odd (G.degree x)} := by
    rw [hs_card] at hs_le_univ
    simpa only [Fintype.card] using hs_le_univ

  omega


omit [Fintype V] [DecidableRel G.Adj] in
private theorem exists_unused_incident_edge_of_unused_edge
    {u v : V} {p : G.Walk u v}
    (hconn : G.Connected)
    {e : Sym2 V}
    (he : e ∈ G.edgeSet)
    (hnot : e ∉ p.edges) :
    ∃ x y : V, x ∈ p.support ∧ G.Adj x y ∧ s(x, y) ∉ p.edges := by
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


private theorem all_non_endpoint_even_of_card_odd_degree_eq_two
    {u v : V}
    (huv : u ≠ v)
    (huOdd : Odd (G.degree u))
    (hvOdd : Odd (G.degree v))
    (hodd : Fintype.card {x : V | Odd (G.degree x)} = 2) :
    ∀ x : V, x ≠ u → x ≠ v → Even (G.degree x) := by
  intro x hxu hxv
  exact even_degree_of_not_endpoint_of_card_odd_degree_eq_two
    (G := G) huv huOdd hvOdd hodd hxu hxv

omit [Fintype V] [DecidableRel G.Adj] in
private theorem MaximalTrail.is_eulerian_of_connected
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



-- MAIN THEOREM
theorem exists_is_eulerian_of_connected_forall_even_degree
    (u₀ : V)
    (hconn : G.Connected)
    (heven : ∀ x : V,
      Even (G.degree x)) :
    ∃ u, ∃ p : G.Walk u u, p.IsEulerian := by
  obtain ⟨u, p, hpmax⟩ :=
    exists_closed_maximalTrail_of_forall_even_degree (G := G) u₀ heven
  exact ⟨u, p, hpmax.is_eulerian_of_connected hconn⟩


-- Proof when we have 2 odd-degree vertices

private theorem MaximalTrailFrom.odd_degree_end_of_ne
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrailFrom p)
    (huv : u ≠ v) :
    Odd (G.degree v) := by
  have hOddCount : Odd (p.edges.countP fun e => v ∈ e) :=
    hpmax.1.odd_countP_edges_right_of_ne huv

  have hCountDegree :
      p.edges.countP (fun e => v ∈ e) =
        @SimpleGraph.degree V G v
          (Subtype.fintype (Membership.mem (G.neighborSet v))) :=
    hpmax.countP_edges_right_eq_degree

  simpa [hCountDegree] using hOddCount

private theorem MaximalTrail.odd_degree_end_of_ne
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p)
    (huv : u ≠ v) :
    Odd (G.degree v) := by
  exact hpmax.to_MaximalTrailFrom.odd_degree_end_of_ne huv

private theorem MaximalTrail.odd_degree_start_of_ne
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p)
    (huv : u ≠ v) :
    Odd (G.degree u) := by
  have hpmaxRev : MaximalTrail p.reverse := by
    constructor
    · exact SimpleGraph.Walk.IsTrail.reverse p hpmax.1
    · intro x y q hq
      have h := hpmax.2 q.reverse (SimpleGraph.Walk.IsTrail.reverse q hq)
      rw [SimpleGraph.Walk.edges_reverse, List.length_reverse] at h
      simpa [SimpleGraph.Walk.edges_reverse, List.length_reverse] using h
  exact hpmaxRev.odd_degree_end_of_ne huv.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem IsTrail.exists_longer_of_unused_closed_detour
    {u v x : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (hx : x ∈ p.support)
    {c : G.Walk x x}
    (hc : c.IsTrail)
    (hcNonempty : c.edges ≠ [])
    (hdisj : c.edges.Disjoint p.edges) :
    ∃ q : G.Walk u v, q.IsTrail ∧ p.edges.length < q.edges.length := by
  classical

  obtain ⟨p₁, p₂, hp_eq⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_append).mp hx

  refine ⟨p₁.append (c.append p₂), ?_, ?_⟩

  · rw [SimpleGraph.Walk.isTrail_def]
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append]

    have hpNodup : (p₁.edges ++ p₂.edges).Nodup := by
      have h := hp.edges_nodup
      rw [hp_eq, SimpleGraph.Walk.edges_append] at h
      exact h

    have hcNodup : c.edges.Nodup := hc.edges_nodup

    have hp₁Nodup : p₁.edges.Nodup :=
      (List.nodup_append.mp hpNodup).1

    have hp₂Nodup : p₂.edges.Nodup :=
      (List.nodup_append.mp hpNodup).2.1

    have hdisj₁₂ : c.edges.Disjoint (p₁.edges ++ p₂.edges) := by
      rw [← SimpleGraph.Walk.edges_append, ← hp_eq]
      exact hdisj

    have hdisj_p₁_p₂ : p₁.edges.Disjoint p₂.edges := by
      intro e he₁ he₂
      exact (List.nodup_append.mp hpNodup).2.2 e he₁ e he₂ rfl

    have hdisj_c_p₁ : c.edges.Disjoint p₁.edges := by
      intro e hec hep₁
      exact hdisj₁₂ hec (List.mem_append_left _ hep₁)

    have hdisj_c_p₂ : c.edges.Disjoint p₂.edges := by
      intro e hec hep₂
      exact hdisj₁₂ hec (List.mem_append_right _ hep₂)

    rw [List.nodup_append]
    constructor
    · exact hp₁Nodup
    constructor
    · rw [List.nodup_append]
      constructor
      · exact hcNodup
      constructor
      · exact hp₂Nodup
      · intro a hac b hbp₂ hab
        subst b
        exact hdisj_c_p₂ hac hbp₂
    · intro a hap₁ b hb hab
      rw [List.mem_append] at hb
      rcases hb with hbc | hbp₂
      · subst b
        exact hdisj_c_p₁ hbc hap₁
      · subst b
        exact hdisj_p₁_p₂ hap₁ hbp₂

  · have hcLenPos : 0 < c.edges.length := by
      cases hce : c.edges with
      | nil =>
          exact False.elim (hcNonempty hce)
      | cons e es =>
          simp

    have hpLen :
        p.edges.length = p₁.edges.length + p₂.edges.length := by
      rw [hp_eq, SimpleGraph.Walk.edges_append, List.length_append]

    have hqLen :
        (p₁.append (c.append p₂)).edges.length =
          p₁.edges.length + c.edges.length + p₂.edges.length := by
      rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append]
      simp [List.length_append, Nat.add_assoc]

    rw [hpLen, hqLen]
    omega


omit [Fintype V] [DecidableRel G.Adj] in
private theorem exists_unused_closed_detour_of_unused_edge_of_incident_detour
    {u v : V} {p : G.Walk u v}
    (hconn : G.Connected)
    {e : Sym2 V}
    (he : e ∈ G.edgeSet)
    (hnot : e ∉ p.edges)
    (hlocal :
      ∀ ⦃x y : V⦄,
        x ∈ p.support →
        G.Adj x y →
        s(x, y) ∉ p.edges →
        ∃ c : G.Walk x x,
          c.IsTrail ∧
          c.edges ≠ [] ∧
          c.edges.Disjoint p.edges) :
    ∃ x : V, ∃ c : G.Walk x x,
      x ∈ p.support ∧
      c.IsTrail ∧
      c.edges ≠ [] ∧
      c.edges.Disjoint p.edges := by
  obtain ⟨x, y, hx, hxy, hxy_unused⟩ :=
    exists_unused_incident_edge_of_unused_edge
      (G := G) (p := p) hconn he hnot

  obtain ⟨c, hc, hcNonempty, hdisj⟩ :=
    hlocal hx hxy hxy_unused

  exact ⟨x, c, hx, hc, hcNonempty, hdisj⟩


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem MaximalTrailAvoidingFrom.length_pos_of_unused_adj_start
    {u v x y z : V} {p : G.Walk u v} {q : G.Walk x z}
    (hqmax : MaximalTrailAvoidingFrom p q)
    (hxy : G.Adj x y)
    (hxy_unused : s(x, y) ∉ p.edges) :
    0 < q.edges.length := by
  classical

  let r : G.Walk x y := SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil

  have hrTrail : r.IsTrail := by
    dsimp [r]
    exact
      (SimpleGraph.Walk.IsTrail.cons
        (w := (SimpleGraph.Walk.nil : G.Walk y y))
        (by simp)
        hxy
        (by simp))

  have hrDisj : r.edges.Disjoint p.edges := by
    intro e her hep
    have heq : e = s(x, y) := by
      dsimp [r] at her
      simpa using her
    exact hxy_unused (by simpa [heq] using hep)

  have hle : r.edges.length ≤ q.edges.length :=
    hqmax.2.2 r hrTrail hrDisj

  have hrLen : r.edges.length = 1 := by
    dsimp [r]

  omega


private theorem IsTrail.even_countP_edges_iff_even_degree_of_endpoint_parity
    {u v x : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (huv : u ≠ v)
    (huOdd : Odd (G.degree u))
    (hvOdd : Odd (G.degree v))
    (hEvenAway : ∀ z : V, z ≠ u → z ≠ v → Even (G.degree z)) :
    Even (p.edges.countP fun e => x ∈ e) ↔ Even (G.degree x) := by
  constructor
  · intro hpEven
    by_cases hxu : x = u
    · subst x
      have h := (hp.even_countP_edges_iff u).mp hpEven
      exact False.elim ((h huv).1 rfl)
    by_cases hxv : x = v
    · subst x
      have h := (hp.even_countP_edges_iff v).mp hpEven
      exact False.elim ((h huv).2 rfl)
    exact hEvenAway x hxu hxv
  · intro hdegEven
    by_cases hxu : x = u
    · subst x
      exact False.elim ((Nat.not_even_iff_odd.mpr huOdd) hdegEven)
    by_cases hxv : x = v
    · subst x
      exact False.elim ((Nat.not_even_iff_odd.mpr hvOdd) hdegEven)
    exact (hp.even_countP_edges_iff x).mpr (by
      intro _
      exact ⟨hxu, hxv⟩)


private theorem MaximalTrailAvoidingFrom.filter_edgesFinset_eq_incidenceFinset_filter_not_mem
    {u v x z : V} {p : G.Walk u v} {q : G.Walk x z}
    (hqmax : MaximalTrailAvoidingFrom p q) :
    hqmax.1.edgesFinset.filter (fun e => z ∈ e) =
      (G.incidenceFinset z).filter (fun e => e ∉ p.edges) := by
  ext e
  constructor
  · intro he
    rw [Finset.mem_filter] at he
    rw [Finset.mem_filter]
    constructor
    · rw [G.incidenceFinset_eq_filter z]
      rw [Finset.mem_filter]
      constructor
      · have heq : e ∈ q.edges := by
          simpa [IsTrail.edgesFinset] using he.1
        have heG : e ∈ G.edgeSet := q.edges_subset_edgeSet heq
        simpa using heG
      · exact he.2
    · intro hep
      have heq : e ∈ q.edges := by
        simpa [IsTrail.edgesFinset] using he.1
      exact hqmax.2.1 heq hep
  · intro he
    rw [Finset.mem_filter] at he
    have hInc : e ∈ G.incidenceFinset z := he.1
    have hnotp : e ∉ p.edges := he.2

    have he' : e ∈ G.edgeSet ∧ z ∈ e := by
      rw [G.incidenceFinset_eq_filter z] at hInc
      simpa using hInc

    rcases exists_adj_of_mem_edgeSet_and_mem (G := G) he'.1 he'.2 with ⟨w, hzw, rfl⟩

    rw [Finset.mem_filter]
    constructor
    · simpa [IsTrail.edgesFinset] using
        hqmax.not_unused_edge_at_end hzw hnotp
    · simp

private theorem IsTrail.filter_edgesFinset_eq_incidenceFinset_filter_mem
    {u v z : V} {p : G.Walk u v}
    (hp : p.IsTrail) :
    hp.edgesFinset.filter (fun e => z ∈ e) =
      (G.incidenceFinset z).filter (fun e => e ∈ p.edges) := by
  ext e
  constructor
  · intro he
    rw [Finset.mem_filter] at he
    rw [Finset.mem_filter]
    constructor
    · rw [G.incidenceFinset_eq_filter z]
      rw [Finset.mem_filter]
      constructor
      · have hep : e ∈ p.edges := by
          simpa [IsTrail.edgesFinset] using he.1
        have heG : e ∈ G.edgeSet := p.edges_subset_edgeSet hep
        simpa using heG
      · exact he.2
    · simpa [IsTrail.edgesFinset] using he.1
  · intro he
    rw [Finset.mem_filter] at he
    have hInc : e ∈ G.incidenceFinset z := he.1
    have hep : e ∈ p.edges := he.2

    have hz : z ∈ e := by
      have hInc' : e ∈ ({e ∈ G.edgeFinset | z ∈ e} : Finset (Sym2 V)) := by
        simpa [G.incidenceFinset_eq_filter z] using hInc
      rw [Finset.mem_filter] at hInc'
      exact hInc'.2

    rw [Finset.mem_filter]
    constructor
    · simpa [IsTrail.edgesFinset] using hep
    · exact hz

private theorem MaximalTrailAvoidingFrom.even_countP_edges_right_of_endpoint_parity
    {u v x z : V} {p : G.Walk u v} {q : G.Walk x z}
    (hp : p.IsTrail)
    (hqmax : MaximalTrailAvoidingFrom p q)
    (huv : u ≠ v)
    (huOdd : Odd (G.degree u))
    (hvOdd : Odd (G.degree v))
    (hEvenAway : ∀ t : V, t ≠ u → t ≠ v → Even (G.degree t)) :
    Even (q.edges.countP fun e => z ∈ e) := by
  classical

  let A : ℕ := ((G.incidenceFinset z).filter (fun e => e ∈ p.edges)).card
  let B : ℕ := ((G.incidenceFinset z).filter (fun e => e ∉ p.edges)).card
  let D : ℕ := (G.incidenceFinset z).card

  have hqCount :
      q.edges.countP (fun e => z ∈ e) = B := by
    rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
    change (hqmax.1.edgesFinset.filter (fun e => z ∈ e)).card = B
    rw [hqmax.filter_edgesFinset_eq_incidenceFinset_filter_not_mem]

  have hpCount :
      p.edges.countP (fun e => z ∈ e) = A := by
    rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
    change (hp.edgesFinset.filter (fun e => z ∈ e)).card = A
    rw [hp.filter_edgesFinset_eq_incidenceFinset_filter_mem]

  have hpartition :
      A + B = D := by
    have h :=
      Finset.card_filter_add_card_filter_not
        (s := G.incidenceFinset z)
        (p := fun e => e ∈ p.edges)
    simpa [A, B, D] using h

  have hparityA_D : Even A ↔ Even D := by
    have hparity :
        Even (p.edges.countP fun e => z ∈ e) ↔ Even (G.degree z) :=
      hp.even_countP_edges_iff_even_degree_of_endpoint_parity
        huv huOdd hvOdd hEvenAway
    rw [hpCount] at hparity
    rw [← SimpleGraph.card_incidenceFinset_eq_degree G z] at hparity
    simpa [A, D] using hparity

  rw [hqCount]
  change Even B

  by_cases hAe : Even A
  · have hDe : Even D := hparityA_D.mp hAe
    rcases hAe with ⟨a, ha⟩
    rcases hDe with ⟨d, hd⟩
    rw [ha, hd] at hpartition
    use d - a
    omega
  · have hDne : ¬ Even D := by
      intro hDe
      exact hAe (hparityA_D.mpr hDe)

    have hAo : Odd A := Nat.not_even_iff_odd.mp hAe
    have hDo : Odd D := Nat.not_even_iff_odd.mp hDne

    rcases hAo with ⟨a, ha⟩
    rcases hDo with ⟨d, hd⟩

    rw [ha, hd] at hpartition
    use d - a
    omega



private theorem MaximalTrailAvoidingFrom.is_closed_of_endpoint_parity
    {u v x z : V} {p : G.Walk u v} {q : G.Walk x z}
    (hp : p.IsTrail)
    (hqmax : MaximalTrailAvoidingFrom p q)
    (huv : u ≠ v)
    (huOdd : Odd (G.degree u))
    (hvOdd : Odd (G.degree v))
    (hEvenAway : ∀ t : V, t ≠ u → t ≠ v → Even (G.degree t)) :
    x = z := by
  by_contra hxz

  have hOddQ : Odd (q.edges.countP fun e => z ∈ e) :=
    hqmax.1.odd_countP_edges_right_of_ne hxz

  have hEvenQ : Even (q.edges.countP fun e => z ∈ e) :=
    hqmax.even_countP_edges_right_of_endpoint_parity
      hp huv huOdd hvOdd hEvenAway

  exact (Nat.not_even_iff_odd.mpr hOddQ) hEvenQ


private theorem exists_closed_trail_disjoint_of_unused_incident_edge
    {u v x y : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (huv : u ≠ v)
    (huOdd : Odd (G.degree u))
    (hvOdd : Odd (G.degree v))
    (hEvenAway : ∀ z : V, z ≠ u → z ≠ v → Even (G.degree z))
    (_hx : x ∈ p.support)
    (hxy : G.Adj x y)
    (hxy_unused : s(x, y) ∉ p.edges) :
    ∃ c : G.Walk x x,
      c.IsTrail ∧
      c.edges ≠ [] ∧
      c.edges.Disjoint p.edges := by
  classical

  obtain ⟨z, q, hqmax⟩ :=
    exists_maximalTrailAvoidingFrom (G := G) p x

  have hqNonempty : q.edges ≠ [] := by
    have hpos : 0 < q.edges.length :=
      hqmax.length_pos_of_unused_adj_start hxy hxy_unused
    intro hnil
    rw [hnil] at hpos
    simp at hpos

  have hxz : x = z :=
    hqmax.is_closed_of_endpoint_parity hp huv huOdd hvOdd hEvenAway

  subst z

  exact ⟨q, hqmax.1, hqNonempty, hqmax.2.1⟩


private theorem exists_unused_closed_detour_of_unused_edge
    {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (hconn : G.Connected)
    (huv : u ≠ v)
    (huOdd : Odd (G.degree u))
    (hvOdd : Odd (G.degree v))
    (hodd : Fintype.card {x : V | Odd (G.degree x)} = 2)
    {e : Sym2 V}
    (he : e ∈ G.edgeSet)
    (hnot : e ∉ p.edges) :
    ∃ x : V, ∃ c : G.Walk x x,
      x ∈ p.support ∧
      c.IsTrail ∧
      c.edges ≠ [] ∧
      c.edges.Disjoint p.edges := by
  apply exists_unused_closed_detour_of_unused_edge_of_incident_detour
    (G := G) (p := p) hconn he hnot
  intro x y hx hxy hxy_unused

  have hEvenAway :
      ∀ z : V, z ≠ u → z ≠ v → Even (G.degree z) :=
    all_non_endpoint_even_of_card_odd_degree_eq_two
      (G := G) huv huOdd hvOdd hodd

  exact exists_closed_trail_disjoint_of_unused_incident_edge
    (G := G) hp huv huOdd hvOdd hEvenAway hx hxy hxy_unused


private theorem MaximalTrail.mem_edges_of_connected
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p)
    (hconn : G.Connected)
    (huv : u ≠ v)
    (huOdd : Odd (G.degree u))
    (hvOdd : Odd (G.degree v))
    (hodd : Fintype.card {x : V | Odd (G.degree x)} = 2) :
    ∀ e ∈ G.edgeSet, e ∈ p.edges := by
  intro e he
  by_contra hnot

  obtain ⟨x, c, hx, hc, hcNonempty, hdisj⟩ :=
    exists_unused_closed_detour_of_unused_edge
      (G := G) hpmax.1 hconn huv huOdd hvOdd hodd he hnot

  obtain ⟨q, hqTrail, hqLong⟩ :=
    hpmax.1.exists_longer_of_unused_closed_detour
      hx hc hcNonempty hdisj

  have hmax := hpmax.2 q hqTrail

  exact Nat.not_lt_of_ge hmax hqLong

private theorem MaximalTrail.isEulerian_of_connected_of_endpoint_odd
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p)
    (hconn : G.Connected)
    (huv : u ≠ v)
    (huOdd : Odd (G.degree u))
    (hvOdd : Odd (G.degree v))
    (hodd : Fintype.card {x : V | Odd (G.degree x)} = 2) :
    p.IsEulerian := by
  exact hpmax.1.isEulerian_of_forall_mem
    (hpmax.mem_edges_of_connected hconn huv huOdd hvOdd hodd)


omit [DecidableEq V] in
private theorem card_odd_degree_eq_zero_of_forall_even_degree
    (heven : ∀ x : V, Even (G.degree x)) :
    Fintype.card {v : V | Odd (G.degree v)} = 0 := by
  classical
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro x
  exact (Nat.not_even_iff_odd.mpr x.property) (heven x)

private theorem MaximalTrail.not_closed_of_connected_card_odd_degree_eq_two
    {u v : V} {p : G.Walk u v}
    (hpmax : MaximalTrail p)
    (hconn : G.Connected)
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 2) :
    u ≠ v := by
  intro huv
  subst v

  have hpEuler : p.IsEulerian :=
    hpmax.is_eulerian_of_connected hconn

  have hEvenAll : ∀ x : V, Even (G.degree x) := by
    intro x
    exact (hpEuler.even_degree_iff (x := x)).mpr (by
      intro huu
      exact False.elim (huu rfl))

  have hzero :
      Fintype.card {v : V | Odd (G.degree v)} = 0 :=
    card_odd_degree_eq_zero_of_forall_even_degree (G := G) hEvenAll

  omega


theorem exists_isEulerian_of_connected_card_oddDegree_eq_two
    (hconn : G.Connected)
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 2) :
    ∃ u v, ∃ p : G.Walk u v, p.IsEulerian := by
  classical

  obtain ⟨u₀⟩ := hconn.nonempty
  obtain ⟨u, v, p, hpmax⟩ := exists_maximalTrail (G := G) u₀

  have huv : u ≠ v :=
    hpmax.not_closed_of_connected_card_odd_degree_eq_two hconn hodd

  have huOdd : Odd (G.degree u) :=
    hpmax.odd_degree_start_of_ne huv

  have hvOdd : Odd (G.degree v) :=
    hpmax.odd_degree_end_of_ne huv

  have hpEuler : p.IsEulerian :=
    hpmax.isEulerian_of_connected_of_endpoint_odd hconn huv huOdd hvOdd hodd

  exact ⟨u, v, p, hpEuler⟩




private theorem MaximalTrail.not_closed_walk_of_connected_card_odd_degree_eq_two
    {u : V} {p : G.Walk u u}
    (hpmax : MaximalTrail p)
    (hconn : G.Connected)
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 2) :
    False := by
  have hne :
      u ≠ u :=
    hpmax.not_closed_of_connected_card_odd_degree_eq_two hconn hodd
  exact hne rfl





  private theorem forall_even_degree_of_card_oddDegree_eq_zero
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 0) :
    ∀ v : V, Even (G.degree v) := by
  classical
  intro v
  by_contra hvEven

  have hvOdd : Odd (G.degree v) :=
    Nat.not_even_iff_odd.mp hvEven

  have hEmpty : IsEmpty {v : V | Odd (G.degree v)} := by
    rw [← Fintype.card_eq_zero_iff]
    exact hodd

  exact False.elim (hEmpty.false ⟨v, hvOdd⟩)


/-- A connected finite graph has an Eulerian trail if it has either no odd-degree vertices
or exactly two odd-degree vertices. This is the converse existence statement to
`SimpleGraph.Walk.IsEulerian.card_odd_degree`. -/
theorem exists_isEulerian_of_connected_card_oddDegree_eq_zero_or_two
    (hconn : G.Connected)
    (hodd : Fintype.card {v : V | Odd (G.degree v)} = 0 ∨
      Fintype.card {v : V | Odd (G.degree v)} = 2) :
    ∃ u v, ∃ p : G.Walk u v, p.IsEulerian := by
  classical
  rcases hodd with hzero | htwo
  · obtain ⟨u₀⟩ := hconn.nonempty

    have heven : ∀ v : V, Even (G.degree v) :=
      forall_even_degree_of_card_oddDegree_eq_zero (G := G) hzero

    obtain ⟨u, p, hp⟩ :=
      exists_is_eulerian_of_connected_forall_even_degree
        (G := G) u₀ hconn heven

    exact ⟨u, u, p, hp⟩

  · exact exists_isEulerian_of_connected_card_oddDegree_eq_two
      (G := G) hconn htwo

end Walk
end SimpleGraph
