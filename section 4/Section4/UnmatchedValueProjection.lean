module

public import Section4.MixedMatchFactors
import all Section4.MixedMatchFactors
import all Section2.SeparatedSets

/-! Projecting unmatched labels onto the value coordinates introduces
no residue parameters. The residue domain may be arbitrary. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2

theorem matchedDomain_definable {T : Type*} {J : Language} [J.Structure T] {G : Set T}
    {I H : Type} [Finite I] [Finite H] {D : Set ((I → T) × (H → T))}
    (hd : G.Definable J (pairedSet D)) : G.Definable J (Prod.fst '' D) := by
  convert hd.image_comp Sum.inl using 1
  ext a
  constructor
  · rintro ⟨⟨x,y⟩,h,rfl⟩
    exact ⟨Sum.elim x y,h,rfl⟩
  · rintro ⟨z,h,rfl⟩
    exact ⟨_,h,rfl⟩

private theorem finiteUnion {T U : Type*} {P : Set T → Prop} {Q : Set U → Prop}
    {I : Type} [Finite I] (D : I → Set (T × U)) (sep : ∀ i, SeparatedSets P Q (D i)) :
    SeparatedSets P Q (⋃ i, D i) := by
  classical
  let _ := Fintype.ofFinite I
  have ind (is : Finset I) : SeparatedSets P Q (⋃ i ∈ is, D i) := by
    induction is using Finset.induction_on with
    | empty => simpa using SeparatedSets.empty (left := P) (right := Q)
    | insert a is _ ih =>
      simpa only [Finset.set_biUnion_insert] using (sep a).union ih
  simpa using ind Finset.univ

private theorem fstDefinable {T U : Type*} {P : Set T → Prop} {Q : Set U → Prop} {D : Set (T × U)}
    (empty : P ∅) (union : ∀ {a b}, P a → P b → P (a ∪ b)) (sep : SeparatedSets P Q D) :
    P (Prod.fst '' D) := by
  induction sep with
  | empty => simpa using empty
  | @insert a b _ ha _ _ ih =>
    rw [Set.image_union]
    by_cases nb : b.Nonempty
    · have h : Prod.fst '' (a ×ˢ b) = a := by
        ext x
        exact ⟨fun ⟨_,h,e⟩ => e ▸ h.1,fun h => ⟨(x,nb.choose),⟨h,nb.choose_spec⟩,rfl⟩⟩
      rw [h]
      exact union ha ih
    · simpa [Set.not_nonempty_iff_eq_empty.mp nb] using ih

theorem unmatched_value_projection {T U : Type*} {J : Language} [J.Structure T] {G : Set T}
    {I N : Type} [Finite N] {D : Set (I → T)} (hd : G.Definable J D) (R : Set U)
    (matchDomain : N → Set ((I → T) × U))
    (separated : ∀ j, SeparatedSets (G.Definable J) (fun _ => True) (matchDomain j)) :
    G.Definable J {a | a ∈ D ∧ ∃ u ∈ R, ∀ j, (a,u) ∉ matchDomain j} := by
  have matched := finiteUnion matchDomain separated
  have rem := SeparatedSets.compl Set.definable_univ trivial (fun h => h.compl) (fun _ => trivial)
    (fun h k => h.inter k) (fun _ _ => trivial) matched
  have valid := SeparatedSets.rect (right := fun _ => True) (V := R) hd trivial
  have sep := SeparatedSets.inter (fun h k => h.inter k) (fun _ _ => trivial) valid rem
  convert fstDefinable Set.definable_empty (fun h k => h.union k) sep using 1
  ext a
  constructor
  · rintro ⟨ha,u,hu,h⟩
    exact ⟨(a,u),⟨⟨ha,hu⟩,fun m => by obtain ⟨j,hj⟩ := Set.mem_iUnion.mp m; exact h j hj⟩,rfl⟩
  · rintro ⟨⟨a,u⟩,⟨⟨ha,hu⟩,h⟩,rfl⟩
    exact ⟨ha,u,hu,fun j hj => h (Set.mem_iUnion.mpr ⟨j,hj⟩)⟩

end GeneralizedEuler.Section4
