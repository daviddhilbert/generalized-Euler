module

public import Section4.MeasurableCharts
import all Section4.FiniteScissors
import all Section4.CanonicalChartMaps
import all Section2.RVDefinableEquivalence

/-! Pack a definable positive graph in twice the ambient degree, record its two
injective coordinate projections, and identify their images. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {k : ℕ} {X T : Type*}
def graphLeft (k : ℕ) : Fin k → Fin (k+k) := fun i => finSumFinEquiv (Sum.inl i)
def graphRight (k : ℕ) : Fin k → Fin (k+k) := fun i => finSumFinEquiv (Sum.inr i)
def packGraph {D E : Set (Fin k → X)} (e : D ≃ E) :=
  {z : Fin (k+k) → X | ∃ x : D, x.val = z ∘ graphLeft k ∧ (e x).val = z ∘ graphRight k}

theorem packed_graph_definable {L : Language} {F : Type*} {Z : TCsort → Type*}
    {M : SortedStructure L F Z} {S : SortedSubstructure M} {D E : Set (Fin k → Z .rv)} (e : D ≃ E)
    (definable : SortedDefinableOver M S.carrier (rvGraph fun x => (e x).val)) :
    isRVSet M S (packGraph e) := by
  let H := {z : Fin k ⊕ Fin k → Z .rv | ∃ x : D, x.val = z ∘ Sum.inl ∧ (e x).val = z ∘ Sum.inr}
  exact isRVSet_precomp (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k+k)) (D := H) definable

theorem packed_graph_all {D E : Set (Fin k → X)} (e : D ≃ E) (P : X → Prop)
    (src : ∀ x ∈ D, ∀ i, P (x i)) (tgt : ∀ x ∈ E, ∀ i, P (x i)) :
    ∀ z ∈ packGraph e, ∀ i, P (z i) := by
  rintro z ⟨x,left,right⟩ j
  obtain ⟨a,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k+k)).surjective j
  cases a with
  | inl i => exact (congrArg P (congrFun left i)).mp (src _ x.property i)
  | inr i => exact (congrArg P (congrFun right i)).mp (tgt _ (e x).property i)

variable (f : T → X) {D E : Set (Fin k → X)} (e : D ≃ E)
def liftedGraph := (fun z : Fin (k+k) → T => f ∘ z) ⁻¹' packGraph e

theorem lifted_graph_injections (hf : Function.Injective f) :
    Set.InjOn (fun z => z ∘ graphLeft k) (liftedGraph f e) ∧
    Set.InjOn (fun z => z ∘ graphRight k) (liftedGraph f e) := by
  have both {z w : Fin (k+k) → T} (a : z ∘ graphLeft k = w ∘ graphLeft k)
      (b : z ∘ graphRight k = w ∘ graphRight k) : z = w := by
    funext j
    obtain ⟨c,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k+k)).surjective j
    cases c with | inl i => exact congrFun a i | inr i => exact congrFun b i
  have cancel {u w : Fin k → T} (eq : f ∘ u = f ∘ w) : u = w := funext fun j => hf (congrFun eq j)
  constructor
  · rintro z ⟨x,hx,ex⟩ w ⟨y,hy,ey⟩ left
    have xy : x = y := Subtype.ext (hx.trans ((congrArg (f ∘ ·) left).trans hy.symm))
    exact both left (cancel (ex.symm.trans ((congrArg (fun t : D => (e t).val) xy).trans ey)))
  · rintro z ⟨x,hx,ex⟩ w ⟨y,hy,ey⟩ right
    have xy : x = y := e.injective (Subtype.ext (ex.trans ((congrArg (f ∘ ·) right).trans ey.symm)))
    exact both (cancel (hx.symm.trans ((congrArg Subtype.val xy).trans hy))) right

theorem lifted_graph_images (source : ∀ x : D, ∃ z, f ∘ z = x.val) (target : ∀ x : E, ∃ z, f ∘ z = x.val) :
    (fun z => z ∘ graphLeft k) '' liftedGraph f e = (fun z => f ∘ z) ⁻¹' D ∧
    (fun z => z ∘ graphRight k) '' liftedGraph f e = (fun z => f ∘ z) ⁻¹' E := by
  let pack (x y : Fin k → T) := Sum.elim x y ∘ finSumFinEquiv.symm
  have L x y : pack x y ∘ graphLeft k = x := funext fun i => by change Sum.elim x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = _; rw [Equiv.symm_apply_apply]; rfl
  have R x y : pack x y ∘ graphRight k = y := funext fun i => by change Sum.elim x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) = _; rw [Equiv.symm_apply_apply]; rfl
  have mem (x : D) (z w : Fin k → T) (hz : f ∘ z = x.val) (hw : f ∘ w = (e x).val) :
      pack z w ∈ liftedGraph f e :=
    ⟨x,hz.symm.trans (congrArg (f ∘ ·) (L z w).symm),hw.symm.trans (congrArg (f ∘ ·) (R z w).symm)⟩
  constructor
  · ext z; constructor
    · rintro ⟨w,⟨x,hx,_⟩,rfl⟩; exact (congrArg (· ∈ D) hx).mp x.property
    · intro hz; let x : D := ⟨_,hz⟩
      obtain ⟨w,hw⟩ := target (e x)
      exact ⟨pack z w,mem x z w rfl hw,L z w⟩
  · ext w; constructor
    · rintro ⟨z,⟨x,_,hx⟩,rfl⟩; exact (congrArg (· ∈ E) hx).mp (e x).property
    · intro hw; let y : E := ⟨_,hw⟩
      obtain ⟨z,hz⟩ := source (e.symm y)
      exact ⟨pack z w,mem (e.symm y) z w hz (congrArg Subtype.val (e.apply_symm_apply y)).symm,R z w⟩

end GeneralizedEuler.Section4
