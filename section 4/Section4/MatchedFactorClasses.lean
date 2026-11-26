module

public import Section4.UnmatchedValueProjection
public import Section4.ValueScissors
import all Section4.MixedMatchFactors
import all Section4.ValueScissors

/-! A graph piece in the factorization gives equal positive classes
of its value projections, in the original ambient degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder ValueObject
variable {T : Type*} {J : Language} [J.Structure T] {G : Set T}
  {I H : Type} [Finite I] [Finite H]

theorem matchedRange_definable {D : Set ((I → T) × (H → T))}
    (hd : G.Definable J (pairedSet D)) : G.Definable J (Prod.snd '' D) := by
  convert hd.image_comp Sum.inr using 1
  ext a
  constructor
  · rintro ⟨⟨x,y⟩,h,rfl⟩
    exact ⟨Sum.elim x y,h,rfl⟩
  · rintro ⟨z,h,rfl⟩
    exact ⟨_,h,rfl⟩

theorem nonempty_factor_graphs {A B C D : Type*}
    {U : Set (A × B)} {W : Set (C × D)} (nu : U.Nonempty) (nw : W.Nonempty)
    (p : {a // ∃ b, (a,b) ∈ U} ≃ {b // ∃ a, (a,b) ∈ U})
    (q : {c // ∃ d, (c,d) ∈ W} ≃ {d // ∃ c, (c,d) ∈ W})
    (graph : ∀ a c b d, (a.val,b.val) ∈ U ∧ (c.val,d.val) ∈ W ↔ p a = b ∧ q c = d) :
    (∀ a b, (a.val,b.val) ∈ U ↔ p a = b) ∧ (∀ c d, (c.val,d.val) ∈ W ↔ q c = d) := by
  obtain ⟨⟨a,b⟩,hab⟩ := nu
  obtain ⟨⟨c,d⟩,hcd⟩ := nw
  let a₀ : {x // ∃ y, (x,y) ∈ U} := ⟨a,b,hab⟩
  let c₀ : {x // ∃ y, (x,y) ∈ W} := ⟨c,d,hcd⟩
  refine ⟨fun u v => ⟨fun h => ((graph u c₀ v ⟨d,c,hcd⟩).mp ⟨h,hcd⟩).1,
    fun h => ((graph u c₀ v (q c₀)).mpr ⟨h,rfl⟩).1⟩,?_⟩
  exact fun x y => ⟨fun h => ((graph a₀ x ⟨b,a,hab⟩ y).mp ⟨hab,h⟩).2,
    fun h => ((graph a₀ x (p a₀) y).mpr ⟨rfl,h⟩).2⟩

theorem matched_value_classes {k : ℕ} {D : Set ((Fin k → T) × (Fin k → T))}
    (hd : G.Definable J (pairedSet D))
    (p : {a // ∃ b, (a,b) ∈ D} ≃ {b // ∃ a, (a,b) ∈ D})
    (graph : ∀ a b, (a.val,b.val) ∈ D ↔ p a = b) :
    pieceClass (Prod.fst '' D) (matchedDomain_definable hd) =
      pieceClass (Prod.snd '' D) (matchedRange_definable hd) := by
  have dom : {a | ∃ b, (a,b) ∈ D} = Prod.fst '' D := by
    ext a; exact ⟨fun ⟨b,h⟩ => ⟨(a,b),h,rfl⟩,fun ⟨⟨a,b⟩,h,e⟩ => e ▸ Exists.intro b h⟩
  have ran : {b | ∃ a, (a,b) ∈ D} = Prod.snd '' D := by
    ext b; exact ⟨fun ⟨a,h⟩ => ⟨(a,b),h,rfl⟩,fun ⟨⟨a,b⟩,h,e⟩ => e ▸ Exists.intro a h⟩
  let castSet {U V : Set (Fin k → T)} (eq : U = V) : U ≃ V :=
    ⟨fun x => ⟨x.val,eq ▸ x.property⟩,fun y => ⟨y.val,eq.symm ▸ y.property⟩,fun _ => rfl,fun _ => rfl⟩
  let q := (castSet dom.symm).trans (p.trans (castSet ran))
  apply pieceClass_iso _ _ q
  convert hd using 1
  ext t
  constructor
  · rintro ⟨a,ha,hb⟩
    let u := castSet dom.symm a
    have h := (graph u (p u)).mpr rfl
    change (t ∘ Sum.inl,t ∘ Sum.inr) ∈ D
    rw [← ha,← hb]
    exact h
  · intro h
    let a : {a // ∃ b, (a,b) ∈ D} := ⟨t ∘ Sum.inl,t ∘ Sum.inr,h⟩
    let b : {b // ∃ a, (a,b) ∈ D} := ⟨t ∘ Sum.inr,t ∘ Sum.inl,h⟩
    exact ⟨castSet dom a,rfl,congrArg Subtype.val ((graph a b).mp h)⟩

end GeneralizedEuler.Section4
