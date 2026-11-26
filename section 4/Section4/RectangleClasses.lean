module

public import Section4.CanonicalChartMaps
public import Section4.PositivePresentations
public import Section4.WholeFiberRelation
import all Section4.Scissors
import all Section4.PositivePresentations
import all Section4.RectangleDecomposition
import all Section4.PositiveRectangles
import all Section4.CanonicalChartMaps
import all Section4.FiniteScissors

/-! The class of one positive chart in its original ambient degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2

theorem rv_equivalent_target_definable {L : Language} {E : Type*} {Z : TCsort → Type*}
    {I H : Type} [Finite I] {M : SortedStructure L E Z} {S : SortedSubstructure M}
    {D : Set (I → Z .rv)} {B : Set (H → Z .rv)} (h : RVDefinablyEquivalent M S.carrier D B) :
    isRVSet M S B := by
  obtain ⟨e,he⟩ := h
  have eq : Set.range (fun x => (e x).val) = B := by
    ext y
    exact ⟨fun ⟨x,hx⟩ => hx ▸ (e x).property,
      fun hy => ⟨e.symm ⟨y,hy⟩,congrArg Subtype.val (e.apply_symm_apply _)⟩⟩
  rw [← eq]; exact definable_range_of_rvGraph _ he

theorem first_factor_definable {L : Language} {E : Type*} {Z : TCsort → Type*}
    {I H : Type} [Finite H] {M : SortedStructure L E Z} {S : SortedSubstructure M}
    {D : Set (I → Z .rv)} {B : Set (H → Z .rv)} (h : isRVSet M S (productSet D B)) (hb : B.Nonempty) :
    isRVSet M S D := by
  have eq : {x | ∃ y : H → Z .rv, Sum.elim x y ∈ productSet D B} = D := by
    ext x
    exact ⟨fun ⟨y,hy⟩ => hy.1,fun hx => ⟨hb.choose,hx,hb.choose_spec⟩⟩
  rw [← eq]; exact isRVSet_project h

variable {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field F]
  (O : ValuationSubring K) [Module F (Additive (PositiveRV O))] [Module F (Additive O.ValueGroupˣ)]
  (v : Additive (PositiveRV O) →ₗ[F] Additive O.ValueGroupˣ)
  (s : Additive O.ValueGroupˣ →ₗ[F] Additive (PositiveRV O)) (hs : v.comp s = LinearMap.id)
  {G : Submodule F (Additive O.ValueGroupˣ)} {J : Language} [J.Structure K] [J.Structure (Residue O)]
  (hO : IsOrderConvex O) (P : F → RV0 O → RV0 O)
  (powers : ∀ e (x : Additive (PositiveRV O)), positiveRVToRV0 O (e • x).toMul = P e (positiveRVToRV0 O x.toMul))
  (S : SortedSubstructure (canonicalStructure (L := J) O hO P))

def positiveSharp {r : ℕ} (D : Set (Fin r → Additive O.ValueGroupˣ)) :=
  codeTuple O '' {z : Fin r → Additive (PositiveRV O) | v ∘ z ∈ D}

theorem positiveSharp_pos {r} (D : Set (Fin r → Additive O.ValueGroupˣ))
    (x : Fin r → RV0 O) (hx : x ∈ positiveSharp O v D) (i : Fin r) : IsPositiveRV O (x i) := by
  obtain ⟨z,_,rfl⟩ := hx
  exact positiveRVToRV0_pos O _

include hs in
theorem positiveSharp_nonempty {r} (D : Set (Fin r → Additive O.ValueGroupˣ)) (h : D.Nonempty) :
    (positiveSharp O v D).Nonempty := by
  obtain ⟨x,hx⟩ := h
  have eq : v ∘ (s ∘ x) = x := funext fun j => DFunLike.congr_fun hs (x j)
  exact ⟨_,s ∘ x,show v ∘ (s ∘ x) ∈ D by rwa [eq],rfl⟩

def codedResidues {r n m} (A : ValueFrame G r n) (e : Fin m ≃ A.dependent)
    (B : Set (A.dependent → v.ker)) :=
  (fun b : A.dependent → v.ker => fun i => positiveRVToRV0 O (b (e i)).val.toMul) '' B

theorem codedResidues_pos {r n m} (A : ValueFrame G r n) (e : Fin m ≃ A.dependent)
    (B : Set (A.dependent → v.ker)) (x : Fin m → RV0 O) (hx : x ∈ codedResidues O v A e B) (i) :
    IsPositiveRV O (x i) := by
  obtain ⟨b,_,rfl⟩ := hx; exact positiveRVToRV0_pos O _

include powers hs in
theorem class_of_positive_chart {m r} (A : ValueFrame G r (m+r)) (e : Fin m ≃ A.dependent)
    (base : ∀ i, positiveRVToRV0 O (s (A.shift i).val).toMul ∈ S.carrier .rv)
    (D : Set (Fin r → Additive O.ValueGroupˣ)) (B : Set (A.dependent → v.ker))
    (nonempty : D.Nonempty) (hd : isRVSet _ S (positiveSharp O v D))
    (U : Set (Fin (m+r) → RV0 O)) (du : isRVSet _ S U) (pos : ∀ x ∈ U, ∀ i, IsPositiveRV O (x i))
    (hU : U = (fun w => codeTuple O (A.assemble v s w.1 w.2)) ''
      ({z : Fin r → Additive (PositiveRV O) | v ∘ z ∈ D} ×ˢ B)) :
    ∃ hb : isRVSet _ S (codedResidues O v A e B),
      objectClass _ S ⟨m+r,positiveObject O hO P S U du pos⟩ =
        objectClass _ S ⟨m,positiveObject O hO P S _ hb (codedResidues_pos O v A e B)⟩ *
        objectClass _ S ⟨r,positiveObject O hO P S _ hd (positiveSharp_pos O v D)⟩ := by
  have definableImage := hU ▸ du
  let W := {z : Fin r → Additive (PositiveRV O) | v ∘ z ∈ D} ×ˢ B
  have equivalent := chart_definably_equivalent O P powers v s A e hO S W base definableImage
  have target := rectangle_image O v A e {z | v ∘ z ∈ D} B
  change codeRectangle O v A e '' W = productSet (codedResidues O v A e B) (positiveSharp O v D) at target
  rw [target,← hU] at equivalent
  have hb := first_factor_definable (rv_equivalent_target_definable equivalent) (positiveSharp_nonempty O v s hs D nonempty)
  exact ⟨hb,scissors_sound _ S (RVRelation.prod _ _ _ equivalent.symm)⟩

end GeneralizedEuler.Section4
