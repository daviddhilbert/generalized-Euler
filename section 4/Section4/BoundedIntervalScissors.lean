module

public import Section4.BoundedValueBoxes
public import Section4.SemiringGroupification
import all Section4.ValueScissors

/-! An interval of any positive base width has class minus the unary
point after groupification. The cut takes place in the actual value
semiring before the identical ray terms are cancelled. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set ValueObject SemiringGroupification
variable {F V : Type*} [Field F] [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V]
  {J : Language} [J.Structure V] (G : Submodule F V) (lang : ValueLanguage (J := J) G)

def intervalPiece (a : V) := {x : Fin 1 → V | 0 < x 0 ∧ x 0 < a}
def upperRay (a : V) := {x : Fin 1 → V | a < x 0}

include lang in
theorem translate_piece (D : Set (Fin 1 → V)) (hd : (G : Set V).Definable J D)
    (a : V) (old : a ∈ G) :
    ∃ h : (G : Set V).Definable J ((fun x : Fin 1 → V => fun i => x i + a) '' D),
      pieceClass _ h = pieceClass D hd := by
  let f (x : Fin 1 → V) i := x i + a
  have defF : (G : Set V).DefinableMap J f := fun i => lang.addFun (Set.DefinableFun.proj J) (J.definableFun_const _ old)
  refine ⟨image_of_map f defF D hd,?_⟩
  have eq := pieceClass_images f (id : (Fin 1 → V) → _) defF (fun _ => Set.DefinableFun.proj J) D hd
    (fun _ _ _ _ e => funext fun i => add_right_cancel (congrFun e i)) Function.injective_id.injOn
  simpa only [Set.image_id] using eq

include lang in
theorem ray_interval_scissors (a : V) (old : a ∈ G) (pos : 0 < a)
    (di : (G : Set V).Definable J (intervalPiece a)) (dr : (G : Set V).Definable J (upperRay 0))
    (dp : (G : Set V).Definable J ({0} : Set (Fin 1 → V))) :
    pieceClass _ dr = (pieceClass _ di + pieceClass _ dp) + pieceClass _ dr := by
  let tr (x : Fin 1 → V) i := x i + a
  let tail := tr '' upperRay (0 : V)
  let pt := tr '' ({0} : Set (Fin 1 → V))
  have tm (x : Fin 1 → V) : x ∈ tail ↔ a < x 0 := by
    constructor
    · rintro ⟨y,hy,rfl⟩; exact lt_add_of_pos_left _ hy
    · intro h; exact ⟨fun i => x i - a,sub_pos.mpr h,funext fun i => sub_add_cancel _ _⟩
  have pm (x : Fin 1 → V) : x ∈ pt ↔ x 0 = a := by
    constructor
    · rintro ⟨y,hy,rfl⟩; rw [Set.mem_singleton_iff.mp hy]; simp [tr]
    · intro h; exact ⟨0,rfl,funext fun i => by simpa [tr,Subsingleton.elim i 0] using h.symm⟩
  obtain ⟨ht,teq⟩ := translate_piece G lang _ dr a old
  obtain ⟨hp,peq⟩ := translate_piece G lang _ dp a old
  have disj : Disjoint (intervalPiece a) pt := Set.disjoint_left.mpr fun x hx p => hx.2.ne ((pm x).mp p)
  have sep : Disjoint (intervalPiece a ∪ pt) tail := by
    apply Set.disjoint_left.mpr; rintro x (h|h) ht'
    · exact h.2.not_gt ((tm x).mp ht')
    · exact ((tm x).mp ht').ne ((pm x).mp h).symm
  have union : (intervalPiece a ∪ pt) ∪ tail = upperRay 0 := by
    ext x
    change (x ∈ intervalPiece a ∨ x ∈ pt) ∨ x ∈ tail ↔ 0 < x 0
    rw [pm,tm]
    change (0 < x 0 ∧ x 0 < a ∨ x 0 = a) ∨ a < x 0 ↔ 0 < x 0
    grind
  calc pieceClass _ dr = pieceClass ((intervalPiece a ∪ pt) ∪ tail) ((di.union hp).union ht) := by congr 1; exact union.symm
       _ = (pieceClass _ di + pieceClass _ dp) + pieceClass _ dr := by
         rw [pieceClass_cut (di.union hp) ht sep,pieceClass_cut di hp disj,teq,peq]

include lang in
theorem bounded_interval_group_class (a : V) (old : a ∈ G) (pos : 0 < a)
    (di : (G : Set V).Definable J (intervalPiece a)) (dr : (G : Set V).Definable J (upperRay 0))
    (dp : (G : Set V).Definable J ({0} : Set (Fin 1 → V))) :
    of _ (pieceClass (intervalPiece a) di) = -of _ (pieceClass {0} dp) := by
  have hcut := ray_interval_scissors G lang a old pos di dr dp
  have eq := congrArg (of _) hcut
  simp only [map_add] at eq
  apply eq_neg_of_add_eq_zero_left
  exact add_right_cancel (eq.symm.trans (zero_add _).symm)

end GeneralizedEuler.Section4
