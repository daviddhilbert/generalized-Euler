module

public import Section4.SliceComparison
import all Section4.SliceComparison
import all Section4.RefinedChartTest
import all Section4.PositiveRectangles
import all Section4.ValueFrames

/-! Stratify the free value domain of any rectangle, including one with
no independent point in its original ambient degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueFrame
open FirstOrder
variable {F V T : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup T] [Module F T]
  {v : T →ₗ[F] V} (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id)
  {G : Submodule F V} {r n : ℕ} {J : Language} [J.Structure V]
  (A : ValueFrame G r n) (D : Set (Fin r → V)) (R : Set (A.dependent → v.ker))

def assemblySet := (fun w => A.assemble v s w.1 w.2) '' ({z | v ∘ z ∈ D} ×ˢ R)

theorem in_assembly (z : Fin r → T) (hz : v ∘ z ∈ D) (b : A.dependent → v.ker) :
    A.assemble v s z b ∈ A.assemblySet s D R ↔ b ∈ R := by
  constructor
  · rintro ⟨⟨w,c⟩,⟨_,hc⟩,eq⟩
    have same := A.assemble_injective v s (a₁ := (w,c)) (a₂ := (z,b)) eq
    exact (congrArg (· ∈ R) (congrArg Prod.snd same)).mp hc
  · intro h; exact ⟨(z,b),⟨hz,h⟩,rfl⟩

variable (c : DefinablePiece J G r)
def subframeChart : ChartPiece v G J n where
  value := ⟨c.rank,A.comp c.frame,c.domain,c.definable,c.independent⟩
  residue := {b | A.residuePart ((A.comp c.frame).padResidue b) ∈ R}

include hs in
theorem subframe_carrier (sub : c.support ⊆ D) :
    (A.subframeChart R c).carrier s = A.assemblySet s D R ∩ {x | (v ∘ x) ∘ A.free ∈ c.support} := by
  let C := A.comp c.frame
  obtain ⟨α,hα,hi⟩ := c.independent
  have hit : C.eval α ∈ Set.range A.eval := ⟨c.frame.eval α,(A.comp_eval c.frame α).symm⟩
  have eval (y : Fin c.rank → V) : C.eval y ∘ A.free = c.frame.eval y := by
    rw [A.comp_eval,A.project_eval]
  have test (z : Fin c.rank → T) (hz : v ∘ z ∈ c.domain) (b : C.dependent → v.ker) :
      C.assemble v s z b ∈ A.assemblySet s D R ↔ A.residuePart (C.padResidue b) ∈ R :=
    A.refine_membership v s hs C α hi hit _ D R (A.in_assembly s D R) z
      (by rw [eval]; exact sub ⟨_,hz,rfl⟩) b
  ext x
  constructor
  · rintro ⟨⟨z,b⟩,⟨hz,hb⟩,rfl⟩
    refine ⟨(test z hz b).mpr hb,?_⟩
    change (v ∘ C.assemble v s z b) ∘ A.free ∈ c.support
    rw [C.assemble_value v s hs z b,eval]; exact ⟨_,hz,rfl⟩
  · rintro ⟨⟨⟨w,b⟩,⟨hw,hb⟩,rfl⟩,hy⟩
    let x := A.assemble v s w b
    obtain ⟨y,hy,eq⟩ := hy
    have ca : v ∘ x = A.eval (v ∘ w) := A.assemble_value v s hs w b
    have proj : (v ∘ x) ∘ A.free = v ∘ w := by rw [ca,A.project_eval]
    have value : v ∘ x = C.eval y := by rw [A.comp_eval,eq,proj,ca]
    have hull : v ∘ x = C.eval ((v ∘ x) ∘ C.free) := by rw [value,C.project_eval]
    let z := x ∘ C.free
    have hz : v ∘ z ∈ c.domain := by change (v ∘ x) ∘ C.free ∈ c.domain; rwa [value,C.project_eval]
    let b' := C.normalize v s hs x hull
    have ex := C.assemble_normalize v s hs x hull
    have old : x ∈ A.assemblySet s D R := ⟨(w,b),⟨hw,hb⟩,rfl⟩
    exact ⟨(z,b'),⟨hz,(test z hz b').mp (ex.symm ▸ old)⟩,ex⟩

include hs in
theorem subframe_partition {l} (c : Fin l → DefinablePiece J G r)
    (cover : ∀ x, x ∈ D ↔ ∃ i, x ∈ (c i).support)
    (disj : Pairwise (fun i j => Disjoint (c i).support (c j).support)) :
    Pairwise (fun i j => Disjoint ((A.subframeChart R (c i)).carrier s) ((A.subframeChart R (c j)).carrier s)) ∧
    (⋃ i, (A.subframeChart R (c i)).carrier s) = A.assemblySet s D R := by
  let U := A.assemblySet s D R
  let f (x : Fin n → T) := (v ∘ x) ∘ A.free
  have cut i : (A.subframeChart R (c i)).carrier s = U ∩ f ⁻¹' (c i).support :=
    A.subframe_carrier s hs D R (c i) (fun x hx => (cover x).mpr ⟨i,hx⟩)
  constructor
  · intro i j ne; rw [cut,cut]; exact ((disj ne).preimage f).mono Set.inter_subset_right Set.inter_subset_right
  · ext x; refine Set.mem_iUnion.trans ⟨?_,?_⟩
    · rintro ⟨i,h⟩; exact ((congrArg (x ∈ ·) (cut i)).mp h).1
    · intro hx
      have val : f x ∈ D := by
        obtain ⟨⟨z,b⟩,⟨hz,_⟩,rfl⟩ := hx
        change (v ∘ A.assemble v s z b) ∘ A.free ∈ D
        rw [A.assemble_value v s hs z b,A.project_eval]; exact hz
      obtain ⟨i,hi⟩ := (cover (f x)).mp val
      exact ⟨i,(congrArg (x ∈ ·) (cut i)).mpr ⟨hx,hi⟩⟩

end GeneralizedEuler.Section4.ValueFrame
