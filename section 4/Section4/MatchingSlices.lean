module

public import Section4.MatchedFactorClasses
public import Section4.MatchingRectangles
import all Section4.CellProducts

/-! A separated matching can be partitioned by its value graph alone.
Consequently each residue graph is a full slice at any pair of values
in the associated nonempty value cell. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2

structure MatchingSlice (A B C D : Type*) where
  values : Set (A × B)
  residues : Set (C × D)
  values_nonempty : values.Nonempty
  residues_nonempty : residues.Nonempty
  valueMap : {a // ∃ b, (a,b) ∈ values} ≃ {b // ∃ a, (a,b) ∈ values}
  residueMap : {u // ∃ w, (u,w) ∈ residues} ≃ {w // ∃ u, (u,w) ∈ residues}
  value_graph : ∀ a b, (a.val,b.val) ∈ values ↔ valueMap a = b
  residue_graph : ∀ u w, (u.val,w.val) ∈ residues ↔ residueMap u = w

theorem matching_slices {A B C D : Type*} {P : Set (A × B) → Prop} {Q : Set (C × D) → Prop}
    (pu : P Set.univ) (pi : ∀ {s t}, P s → P t → P (s ∩ t))
    (pc : ∀ {s}, P s → P sᶜ) (qe : Q ∅) (qu : ∀ {s t}, Q s → Q t → Q (s ∪ t))
    {R : Set ((A × B) × (C × D))} (sep : SeparatedSets P Q R)
    (single : ∀ {a b b' u w w'}, ((a,b),u,w) ∈ R → ((a,b'),u,w') ∈ R → b = b' ∧ w = w')
    (inj : ∀ {a a' b u u' w}, ((a,b),u,w) ∈ R → ((a',b),u',w) ∈ R → a = a' ∧ u = u') :
    ∃ (n : ℕ) (q : Fin n → MatchingSlice A B C D),
      (∀ t, P (q t).values ∧ Q (q t).residues) ∧ Pairwise (fun i j => Disjoint (q i).values (q j).values) ∧
      R = ⋃ t, (q t).values ×ˢ (q t).residues ∧
      ∀ t x, x ∈ (q t).values → ∀ u, u ∈ (q t).residues ↔ (x,u) ∈ R := by
  classical
  obtain ⟨n,V,U,defs,unique,cell⟩ := separated_partition pu pi pc qe qu sep
  let I := {i : Fin n // (V i).Nonempty ∧ (U i).Nonempty}
  have make (i : I) : ∃ t : MatchingSlice A B C D, t.values = V i ∧ t.residues = U i := by
    obtain ⟨np,nq⟩ := i.property
    have hit {a b u w} (v : (a,b) ∈ V i) (r : (u,w) ∈ U i) : ((a,b),u,w) ∈ R := (cell _ _ _ v).mpr r
    obtain ⟨p,q,h⟩ := factor_matching_rectangle (fun a b => (a,b) ∈ V i) (fun u w => (u,w) ∈ U i)
      (by obtain ⟨⟨a,b⟩,v⟩ := np; exact ⟨a,b,v⟩) (by obtain ⟨⟨u,w⟩,r⟩ := nq; exact ⟨u,w,r⟩)
      (fun v r v' r' => single (hit v r) (hit v' r')) (fun v r v' r' => inj (hit v r) (hit v' r'))
    have graphs := nonempty_factor_graphs np nq p q h
    exact ⟨⟨V i,U i,np,nq,p,q,graphs.1,graphs.2⟩,rfl,rfl⟩
  choose q hv hu using make
  let e := (Fintype.equivFin I).symm
  refine ⟨_,q ∘ e,fun t => by simpa only [Function.comp_apply,hv,hu] using defs (e t),?_,?_,?_⟩
  · intro t t' ne
    apply Set.disjoint_left.mpr
    intro x h h'
    rw [Function.comp_apply,hv] at h h'
    obtain ⟨_,_,uniq⟩ := unique x
    exact ne (e.injective (Subtype.ext ((uniq _ h).trans (uniq _ h').symm)))
  · ext z
    simp only [Set.mem_iUnion,Function.comp_apply,hv,hu,Set.mem_prod]
    constructor
    · intro hz
      obtain ⟨t,ht,_⟩ := unique z.1
      have u := (cell _ _ _ ht).mp hz
      let i : I := ⟨t,⟨_,ht⟩,⟨_,u⟩⟩
      exact ⟨e.symm i,by simpa [i] using And.intro ht u⟩
    · rintro ⟨t,v,u⟩
      exact (cell _ _ _ v).mpr u
  · intro t x hx u
    rw [Function.comp_apply,hv] at hx
    rw [Function.comp_apply,hu]
    exact (cell _ _ _ hx).symm

end GeneralizedEuler.Section4
