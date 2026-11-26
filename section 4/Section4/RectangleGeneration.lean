module

public import Section4.RectangleClasses
public import Section4.CommonValueRefinement
import all Section4.PositivePresentations
import all Section4.RectangleClasses
import all Section4.RectangleDecomposition
import all Section4.ValueStratification
import all Section4.FiniteScissors
import all Section4.Objects

/-! From a positive value partition to the sum of products in the concrete RV semiring. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  {G : Submodule F (Additive O.ValueGroupˣ)} {J : Language} [J.Structure K] [J.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))
  (base : ∀ γ : G, positiveRVToRV0 O (s γ.val).toMul ∈ S.carrier .rv)
  {JG : Language} [JG.Structure (Additive O.ValueGroupˣ)] (lang : ValueLanguage (J := JG) G)
  (pull : ∀ {r} {D : Set (Fin r → Additive O.ValueGroupˣ)}, (G : Set _).Definable JG D →
    isRVSet _ S (positiveSharp O v D))

private theorem exists_code {n} (x : Fin n → RV0 O) (pos : ∀ i, IsPositiveRV O (x i)) :
    ∃ z, codeTuple O z = x := by
  choose z hz using fun i => exists_positiveRV_of_positive O (pos i)
  exact ⟨fun i => Additive.ofMul (z i),funext hz⟩

include lang pull in
theorem positive_partition_sets {n l} (U : Set (Fin n → RV0 O)) (hU : isRVSet _ S U)
    (pos : ∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) {Q : Set (Fin n → v.ker) → Prop}
    (p : Fin l → PositivePiece v G (fun _ D => (G : Set _).Definable JG D) Q)
    (supports : ∀ γ, ∃! i, γ ∈ (p i).value.support)
    (charts : ∀ i, ∃ e : (p i).rectangle ≃ (p i).carrier ((codeTuple O) ⁻¹' U), ∀ z,
      (e z).val = (p i).value.frame.assemble v s z.1.val z.2.val) :
    ∃ C : Fin l → Set (Fin n → RV0 O), (∀ i, isRVSet _ S (C i)) ∧
      (∀ i x, x ∈ C i → ∀ j, IsPositiveRV O (x j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ i, C i) = U ∧
      ∀ i, C i = (fun w => codeTuple O ((p i).value.frame.assemble v s w.1 w.2)) ''
        ({z | v ∘ z ∈ (p i).value.domain} ×ˢ (p i).residues) := by
  classical
  let M := canonicalStructure (L := J) O hO P
  let C i := U ∩ positiveSharp O v (p i).value.support
  have hc i : isRVSet M S (C i) := hU.inter (pull (support_definable lang _))
  have pc i x (hx : x ∈ C i) := pos x hx.1
  have precise (i) (z : Fin n → Additive (PositiveRV O)) :
      codeTuple O z ∈ C i ↔ z ∈ (p i).carrier ((codeTuple O) ⁻¹' U) := by
    change (_ ∧ ∃ w, _ ∧ codeTuple O w = codeTuple O z) ↔ _ ∧ _
    exact and_congr_right fun _ => ⟨fun ⟨w,hw,eq⟩ => codeTuple_injective O eq ▸ hw,fun h => ⟨z,h,rfl⟩⟩
  have cover : ⋃ i, C i = U := by
    ext x; rw [Set.mem_iUnion]
    refine ⟨fun ⟨i,h⟩ => h.1,fun h => ?_⟩
    obtain ⟨z,rfl⟩ := exists_code O x (pos x h)
    obtain ⟨i,hi,_⟩ := supports (v ∘ z)
    exact ⟨i,(precise i z).mpr ⟨h,hi⟩⟩
  have disj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j ne
    apply Set.disjoint_left.mpr
    rintro x hi hj
    obtain ⟨z,rfl⟩ := exists_code O x (pos x hi.1)
    exact ne ((supports (v ∘ z)).unique ((precise i z).mp hi).2 ((precise j z).mp hj).2)
  have images (i) : C i = (fun w => codeTuple O ((p i).value.frame.assemble v s w.1 w.2)) ''
      ({z | v ∘ z ∈ (p i).value.domain} ×ˢ (p i).residues) := by
    obtain ⟨e,he⟩ := charts i
    ext x
    constructor
    · intro hx
      obtain ⟨z,rfl⟩ := exists_code O x (pos x hx.1)
      let a := e.symm ⟨z,(precise i z).mp hx⟩
      have eq : (p i).value.frame.assemble v s a.1.val a.2.val = z :=
        (he a).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))
      exact ⟨(a.1.val,a.2.val),⟨a.1.property,a.2.property⟩,congrArg (codeTuple O) eq⟩
    · rintro ⟨⟨z,b⟩,⟨hz,hb⟩,rfl⟩
      let a : (p i).rectangle := (⟨z,hz⟩,⟨b,hb⟩)
      exact (precise i _).mpr (he a ▸ (e a).property)
  exact ⟨C,hc,pc,disj,cover,images⟩

include hs powers base lang pull in
theorem positive_partition_class {n l} (U : Set (Fin n → RV0 O)) (hU : isRVSet _ S U)
    (pos : ∀ x ∈ U, ∀ i, IsPositiveRV O (x i)) {Q : Set (Fin n → v.ker) → Prop}
    (p : Fin l → PositivePiece v G (fun _ D => (G : Set _).Definable JG D) Q)
    (supports : ∀ γ, ∃! i, γ ∈ (p i).value.support)
    (charts : ∀ i, ∃ e : (p i).rectangle ≃ (p i).carrier ((codeTuple O) ⁻¹' U), ∀ z,
      (e z).val = (p i).value.frame.assemble v s z.1.val z.2.val) :
    ∃ (b : ∀ i, Set (Fin (n-(p i).value.rank) → RV0 O))
      (hb : ∀ i, isRVSet _ S (b i)) (pb : ∀ i x, x ∈ b i → ∀ j, IsPositiveRV O (x j)),
      (∀ i, ∃ e : Fin (n-(p i).value.rank) ≃ (p i).value.frame.dependent,
        b i = codedResidues O v (p i).value.frame e (p i).residues) ∧
      objectClass _ S ⟨n,positiveObject O hO P S U hU pos⟩ =
        ∑ i, objectClass _ S ⟨_,positiveObject O hO P S _ (hb i) (pb i)⟩ *
          objectClass _ S ⟨_,positiveObject O hO P S _ (pull (p i).value.definable)
            (positiveSharp_pos O v (p i).value.domain)⟩ := by
  classical
  let M := canonicalStructure (L := J) O hO P
  obtain ⟨C,hc,pc,disj,cover,images⟩ := positive_partition_sets O v s hO P S lang @pull U hU pos p supports charts
  let m (i) := n-(p i).value.rank
  let idx (i) : Fin (m i) ≃ (p i).value.frame.dependent :=
    (Fintype.equivFinOfCardEq (complement_count (p i).value.frame.free)).symm
  let b i := codedResidues O v (p i).value.frame (idx i) (p i).residues
  have pb i := codedResidues_pos O v (p i).value.frame (idx i) (p i).residues
  have piece (i) : ∃ hb : isRVSet M S (b i),
      objectClass M S ⟨n,positiveObject O hO P S (C i) (hc i) (pc i)⟩ =
        objectClass M S ⟨_,positiveObject O hO P S _ hb (pb i)⟩ *
        objectClass M S ⟨_,positiveObject O hO P S _ (pull (p i).value.definable) (positiveSharp_pos O v _)⟩ := by
    have single {m r n} (A : ValueFrame G r n) (e : Fin m ≃ A.dependent)
        (eq : m+r = n) (D : Set (Fin r → Additive O.ValueGroupˣ)) (R : Set (A.dependent → v.ker))
        (hD : D.Nonempty) (defD : isRVSet M S (positiveSharp O v D))
        (W : Set (Fin n → RV0 O)) (hw : isRVSet M S W) (pw : ∀ x ∈ W, ∀ j, IsPositiveRV O (x j))
        (image : W = (fun w => codeTuple O (A.assemble v s w.1 w.2)) '' ({z | v ∘ z ∈ D} ×ˢ R)) :
        ∃ hR : isRVSet M S (codedResidues O v A e R),
          objectClass M S ⟨n,positiveObject O hO P S W hw pw⟩ =
            objectClass M S ⟨m,positiveObject O hO P S _ hR (codedResidues_pos O v A e R)⟩ *
            objectClass M S ⟨r,positiveObject O hO P S _ defD (positiveSharp_pos O v D)⟩ := by
      subst n
      exact class_of_positive_chart O v s hs hO P powers S A e (fun j => base (A.shift j)) D R hD defD W hw pw image
    have le := Fintype.card_le_of_injective (p i).value.frame.free (p i).value.frame.free.injective
    simp only [Fintype.card_fin] at le
    exact single _ (idx i) (Nat.sub_add_cancel le) _ _ ⟨_,(p i).value.independent.choose_spec.1⟩ _ _ _ _ (images i)
  choose hb weights using piece
  refine ⟨b,hb,pb,fun i => ⟨idx i,rfl⟩,?_⟩
  let obj := positiveObject O hO P S U hU pos
  have sum := objectClass_partition obj C hc disj cover
  refine sum.trans (Finset.sum_congr rfl fun i _ => Eq.trans ?_ (weights i))
  exact scissors_sound M S (RVRelation.iso _ _ ⟨Equiv.refl _,definable_identity_label M S (hc i)⟩)

end GeneralizedEuler.Section4
