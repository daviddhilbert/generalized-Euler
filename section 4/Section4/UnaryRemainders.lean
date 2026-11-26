module

public import Section4.UnaryTaggedComparison
public import Section4.SignedValueGeneration
import all Section4.UnaryTaggedComparison
import all Section4.SignedValueGeneration
import all Section4.Factors

/-! Finiteness and individual fixed-base definability of the unmatched
labels in Question 4.16, retaining the disjoint-union tags and signs. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder ValueObject
variable {Z : Type} [Fintype Z] {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {J H : Language} [J.Structure V] [H.Structure (Z × V)] (G : Submodule F V)
  (A : Set (Z × V)) (interpret : SignedInterpretation (J := J) (H := H) (G : Set V) A)

omit [Fintype Z] in
include interpret in
theorem old_signed_tuple_definable {k} (x : Fin k → Z × V) (old : ∀ i, (x i).2 ∈ G) :
    A.Definable H ({x} : Set (Fin k → Z × V)) := by
  let y := Prod.snd ∘ x
  have defY : (G : Set V).Definable J ({y} : Set (Fin k → V)) := by
    convert Set.definable_iInter_of_finite (fun i => (Set.DefinableFun.proj (A := (G : Set V)) J (i := i)).ofPred_eq_const (old i)) using 1
    ext z; simp [y,funext_iff]
  have eq : signInsert (Prod.fst ∘ x) y = x := rfl
  simpa only [Set.image_singleton,eq] using signed_stratum_definable (G : Set V) A @interpret (Prod.fst ∘ x) {y} defY

include interpret in
theorem old_signed_unary_finite
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set V).Definable J D))
    (D : Set (Fin 1 → Z × V)) (defD : A.Definable H D) (old : ∀ z ∈ D, (z 0).2 ∈ G) :
    D.Finite := by
  let s (b : Fin 1 → Z) := signInsert b ⁻¹' D
  have finite b : (s b).Finite := finite_unmatched_unary G sat (s b) ((interpret D).mp defD b)
    (fun z hz => old (signInsert b z) hz)
  apply (Set.finite_iUnion (fun b => (finite b).image (signInsert b))).subset
  intro z hz
  exact Set.mem_iUnion.mpr ⟨Prod.fst ∘ z,Prod.snd ∘ z,hz,rfl⟩

variable (U W : Over (J := H) A 1)

def tagSlice (D : Set (U.points A)) (i : Fin U.tags) : Set (Fin 1 → Z × V) :=
  {z | ∃ h : z ∈ U.piece i, (⟨i,z,h⟩ : U.points A) ∈ D}

include interpret in
theorem old_unary_tags_finite
    (sat : RealizesAffineAvoidance G (fun _ D => (G : Set V).Definable J D))
    (D : Set (U.points A)) (defD : ∀ i, A.Definable H (tagSlice A U D i))
    (old : ∀ p ∈ D, (pointTuple U p 0).2 ∈ G) : D.Finite := by
  let slice (i : Fin U.tags) := tagSlice A U D i
  have fs (i) : (slice i).Finite := old_signed_unary_finite G A @interpret sat _ (defD i)
    (fun z ⟨hz,h⟩ => old ⟨i,z,hz⟩ h)
  let put (i : Fin U.tags) (p : slice i) : U.points A := ⟨i,p.val,p.property.choose⟩
  have fin (i) : (Set.range (put i)).Finite := by
    let := (fs i).fintype
    exact Set.finite_range _
  apply (Set.finite_iUnion fin).subset
  rintro ⟨i,z⟩ hz
  exact Set.mem_iUnion.mpr ⟨i,⟨z.val,z.property,hz⟩,rfl⟩

omit [Fintype Z] [AddCommGroup V] in
theorem tagged_relation_remainder (R : U.points A → W.points A → Prop)
    (defR : ∀ i j, A.Definable H (taggedGraph U W R i j)) (i : Fin U.tags) :
    A.Definable H (tagSlice A U {x | ¬ ∃ y, R x y} i) := by
  let domain := ⋃ j, ((fun t : Fin 1 ⊕ Fin 1 → Z × V => t ∘ Sum.inl) '' taggedGraph U W R i j)
  have hd : A.Definable H domain := Set.definable_iUnion_of_finite fun j => (defR i j).image_comp Sum.inl
  convert (U.isDefinable i).inter hd.compl using 1
  ext z; constructor
  · rintro ⟨hz,miss⟩
    refine ⟨hz,?_⟩
    intro h
    obtain ⟨j,t,⟨x,hx,y,_,hr⟩,rfl⟩ := Set.mem_iUnion.mp h
    have same : x = ⟨_,hz⟩ := Subtype.ext hx
    exact miss ⟨⟨j,y⟩,same ▸ hr⟩
  · rintro ⟨hz,miss⟩
    refine ⟨hz,?_⟩
    rintro ⟨⟨j,y⟩,hr⟩
    exact miss (Set.mem_iUnion.mpr ⟨j,Sum.elim z y.val,⟨⟨z,hz⟩,rfl,y,rfl,hr⟩,rfl⟩)

end GeneralizedEuler.Section4
