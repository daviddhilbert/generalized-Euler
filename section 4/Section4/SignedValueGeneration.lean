module

public import Section4.TaggedValueClasses
public import Section4.ValueEmbedding
import all Section4.ValueScissors
import all Section4.Factors
import all Section4.DegreeZeroInclusion

/-! The signed value group is the finite disjoint union of copies of its
positive part. Definability is tested on each sign tuple in the induced
ordered-vector-space structure. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueObject
open FirstOrder
variable {Z : Type} {V : Type*} [Fintype Z] {J H : Language} [J.Structure V] [H.Structure (Z × V)]
  (G : Set V) (A : Set (Z × V)) (one : Z)

def signInsert {I : Type} (b : I → Z) (x : I → V) := fun i => (b i,x i)

omit [Fintype Z] in
theorem signInsert_inj {I : Type} (b : I → Z) : Function.Injective (signInsert (V := V) b) :=
  fun _ _ h => funext fun i => congrArg Prod.snd (congrFun h i)

@[expose] def SignedInterpretation : Prop := ∀ {I : Type} [Fintype I] (D : Set (I → Z × V)),
  A.Definable H D ↔ ∀ b : I → Z, G.Definable J (signInsert b ⁻¹' D)

variable (interpret : SignedInterpretation (J := J) (H := H) G A)
omit [Fintype Z] in
include interpret in
theorem signed_stratum_definable {k} (b : Fin k → Z) (D : Set (Fin k → V)) (hd : G.Definable J D) :
    A.Definable H (signInsert b '' D) := by
  apply (interpret _).mpr
  intro c
  by_cases h : b=c
  · subst c; simpa [(signInsert_inj (V := V) b).preimage_image] using hd
  · have eq : signInsert c ⁻¹' (signInsert b '' D) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨_,_,eq⟩ => h (funext fun i => congrArg Prod.fst (congrFun eq i))
    rw [eq]; exact Set.definable_empty

omit [Fintype Z] in
include interpret in
theorem sign_strata_iso {k} (b c : Fin k → Z) (D : Set (Fin k → V)) (hd : G.Definable J D) :
    pieceClass (signInsert b '' D) (signed_stratum_definable G A @interpret b D hd) =
    pieceClass (signInsert c '' D) (signed_stratum_definable G A @interpret c D hd) := by
  let B := Equiv.Set.imageOfInjOn (signInsert b) D (signInsert_inj b).injOn
  let E := Equiv.Set.imageOfInjOn (signInsert c) D (signInsert_inj c).injOn
  let e := B.symm.trans E
  apply pieceClass_iso _ _ e
  let R := {w : Fin k ⊕ Fin k → Z × V | ∃ x : signInsert b '' D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr}
  apply (interpret R).mpr
  intro s
  let T := {w : Fin k ⊕ Fin k → V | w ∘ Sum.inl ∈ D ∧ w ∘ Sum.inl = w ∘ Sum.inr}
  have law (w : Fin k ⊕ Fin k → V) : signInsert s w ∈ R ↔ s ∘ Sum.inl = b ∧ s ∘ Sum.inr = c ∧ w ∈ T := by
    constructor
    · rintro ⟨x,hx,hy⟩
      obtain ⟨a,rfl⟩ := B.surjective x
      change (E (B.symm (B a))).val = _ at hy; rw [B.symm_apply_apply] at hy
      have l : a.val = w ∘ Sum.inl := funext fun i => congrArg Prod.snd (congrFun hx i)
      have r : a.val = w ∘ Sum.inr := funext fun i => congrArg Prod.snd (congrFun hy i)
      exact ⟨funext (fun i => (congrArg Prod.fst (congrFun hx i)).symm),
        funext (fun i => (congrArg Prod.fst (congrFun hy i)).symm),(congrArg (· ∈ D) l).mp a.property,l.symm.trans r⟩
    · rintro ⟨hb,hc,hd',eq⟩
      let a : D := ⟨w ∘ Sum.inl,hd'⟩
      refine ⟨B a,funext (fun i => Prod.ext (congrFun hb i).symm rfl),?_⟩
      change (E (B.symm (B a))).val = _; rw [B.symm_apply_apply]
      exact funext fun i => Prod.ext (congrFun hc i).symm (congrFun eq i)
  by_cases h : s ∘ Sum.inl = b ∧ s ∘ Sum.inr = c
  · have eq : signInsert s ⁻¹' R = T := Set.ext fun w => (law w).trans (by simp [h.1,h.2])
    rw [eq]; exact graph_of_map id (fun _ => Set.DefinableFun.proj J) D hd
  · have eq : signInsert s ⁻¹' R = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        fun w hw => h ⟨((law w).mp hw).1,((law w).mp hw).2.1⟩
    rw [eq]; exact Set.definable_empty

include interpret in
theorem signed_piece_decomposition {k} (D : Set (Fin k → Z × V)) (hd : A.Definable H D) :
    pieceClass D hd = ∑ b : Fin k → Z, pieceClass (signInsert (fun _ => one) '' (signInsert b ⁻¹' D))
      (signed_stratum_definable G A @interpret _ _ ((interpret D).mp hd b)) := by
  let C b := signInsert b '' (signInsert b ⁻¹' D)
  have defC b : A.Definable H (C b) := signed_stratum_definable G A @interpret _ _ ((interpret D).mp hd b)
  have disj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j ne; apply Set.disjoint_left.mpr; rintro _ ⟨x,_,rfl⟩ ⟨y,_,eq⟩
    exact ne (funext fun a => (congrArg Prod.fst (congrFun eq a)).symm)
  have cv : (⋃ b, C b) = D := by
    ext x; rw [Set.mem_iUnion]
    exact ⟨fun ⟨_,_,hx,eq⟩ => eq ▸ hx,fun h => ⟨Prod.fst ∘ x,Prod.snd ∘ x,h,rfl⟩⟩
  have cut := pieceClass_partition C defC disj
  have cong {X Y : Set (Fin k → Z × V)} (eq : X=Y) (hx : A.Definable H X) (hy : A.Definable H Y) :
      pieceClass X hx = pieceClass Y hy := by subst Y; rfl
  exact (cong cv.symm _ _).trans (cut.trans (Finset.sum_congr rfl fun b _ => sign_strata_iso G A @interpret b (fun _ => one) _ ((interpret D).mp hd b)))

end GeneralizedEuler.Section4.ValueObject
