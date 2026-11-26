module

public import Section4.FrameComparison
public import Section4.CoordinateChanges
import all Section4.PositiveRectangles

/-! Under a refinement, normalized fine residues split into the old residue
coordinates and unrestricted coordinates measuring the lost value rank. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F V T : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup T] [Module F T] {G : Submodule F V} {n r k : ℕ}

def rowsLinear {i j : Type*} [Fintype i] (A : Matrix j i F) : (i → T) →ₗ[F] (j → T) where
  toFun := actRows A
  map_add' x y := by funext k; simp [actRows,smul_add,Finset.sum_add_distrib]
  map_smul' a x := by funext k; simp [actRows,Finset.smul_sum,smul_smul,mul_comm]

namespace ValueFrame
variable (A : ValueFrame G r n) (B : ValueFrame G k n)

/-- Residue vectors with zero free entries are canonical representatives
modulo the directions of the frame. -/
def residual (x : Fin n → T) : Fin n → T := x - actRows A.rows (x ∘ A.free)

theorem direction_free (z : Fin r → T) : actRows A.rows z ∘ A.free = z := by
  funext i; simp [actRows,A.freeRow,ite_smul]

theorem residual_free (x : Fin n → T) : A.residual x ∘ A.free = 0 := by
  change (x ∘ A.free) - (actRows A.rows (x ∘ A.free) ∘ A.free) = 0
  rw [A.direction_free,sub_self]

theorem residual_add_dir (x : Fin n → T) (z : Fin r → T) :
    A.residual (x + actRows A.rows z) = A.residual x := by
  have free : (x + actRows A.rows z) ∘ A.free = x ∘ A.free + z := by
    exact congrArg (x ∘ A.free + ·) (A.direction_free z)
  unfold residual
  rw [free,show actRows A.rows (x ∘ A.free + z) =
      actRows A.rows (x ∘ A.free) + actRows A.rows z from (rowsLinear A.rows).map_add _ _]
  abel

def padResidue (b : A.dependent → T) (i : Fin n) : T := by
  classical exact if h : i ∉ Set.range A.free then b ⟨i,h⟩ else 0

omit [Module F T] in
theorem pad_free (b : A.dependent → T) : A.padResidue b ∘ A.free = 0 := by
  funext i; simp [padResidue]

omit [Module F T] in
theorem pad_restrict {x : Fin n → T} (hx : x ∘ A.free = 0) :
    A.padResidue (fun i : A.dependent => x i.val) = x := by
  classical
  funext i
  by_cases hi : i ∈ Set.range A.free
  · obtain ⟨j,rfl⟩ := hi; simpa [padResidue] using (congrFun hx j).symm
  · simp [padResidue,hi]

def residuePart (x : Fin n → T) (i : A.dependent) : T := A.residual x i.val

theorem reconstitute (x : Fin n → T) :
    A.padResidue (A.residuePart x) + actRows A.rows (x ∘ A.free) = x := by
  rw [show A.padResidue (A.residuePart x) = A.residual x from A.pad_restrict (A.residual_free x)]
  exact sub_add_cancel _ _

theorem residuePart_pad (b : A.dependent → T) : A.residuePart (A.padResidue b) = b := by
  funext i
  simp [residuePart,residual,A.pad_free,actRows,padResidue,i.property]

theorem residuePart_direction (x : Fin n → T) (z : Fin r → T) :
    A.residuePart (x + actRows A.rows z) = A.residuePart x :=
  congrArg (fun t : Fin n → T => t ∘ Subtype.val) (A.residual_add_dir x z)

variable (C : Matrix (Fin r) (Fin k) F) (relation : B.rows = A.rows * C)
include relation

/-- Refinement identifies fine residues with a product over the old residues.
The second factor is the quotient of the old free residue coordinates by
the projected fine directions. -/
def relativeResidueEquiv :
    (B.dependent → T) ≃ (A.dependent → T) × ((Fin r → T) ⧸ LinearMap.range (rowsLinear (T := T) C)) := by
  let W := LinearMap.range (rowsLinear (T := T) C)
  let project (x : Fin n → T) := (A.residuePart x,W.mkQ (x ∘ A.free))
  have stable (x : Fin n → T) (z : Fin k → T) : project (x + actRows B.rows z) = project x := by
    have dirs : actRows B.rows z = actRows A.rows (actRows C z) := by rw [relation,actRows_mul]
    apply Prod.ext
    · exact dirs ▸ A.residuePart_direction x (actRows C z)
    · change W.mkQ ((x + actRows B.rows z) ∘ A.free) = _
      rw [dirs]
      change W.mkQ ((x ∘ A.free) + (actRows A.rows (actRows C z) ∘ A.free)) = _
      rw [A.direction_free,map_add,show W.mkQ (actRows C z) = 0 from
        (Submodule.Quotient.mk_eq_zero W).mpr ⟨z,rfl⟩,add_zero]
  have reduce (x : Fin n → T) : project (B.padResidue (B.residuePart x)) = project x :=
    (stable _ (x ∘ B.free)).symm.trans (congrArg project (B.reconstitute x))
  apply Equiv.ofBijective (fun b => project (B.padResidue b))
  constructor
  · intro b c eq
    let x := B.padResidue b
    let y := B.padResidue c
    have hres : A.residuePart x = A.residuePart y := congrArg Prod.fst eq
    have hq : W.mkQ (x ∘ A.free - y ∘ A.free) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr (congrArg Prod.snd eq)
    obtain ⟨z,hz⟩ := (Submodule.Quotient.mk_eq_zero W).mp hq
    have dir : actRows B.rows z = actRows A.rows (x ∘ A.free) - actRows A.rows (y ∘ A.free) := by
      rw [relation,actRows_mul,show actRows C z = x ∘ A.free - y ∘ A.free from hz]
      exact (rowsLinear (T := T) A.rows).map_sub _ _
    have xy : x = y + actRows B.rows z := by
      calc
        x = A.padResidue (A.residuePart y) + actRows A.rows (x ∘ A.free) := hres ▸ (A.reconstitute x).symm
        _ = (A.padResidue (A.residuePart y) + actRows A.rows (y ∘ A.free)) + actRows B.rows z := by rw [dir]; abel
        _ = _ := congrArg (· + actRows B.rows z) (A.reconstitute y)
    calc
      b = B.residuePart x := (B.residuePart_pad b).symm
      _ = B.residuePart (y + actRows B.rows z) := congrArg B.residuePart xy
      _ = B.residuePart y := B.residuePart_direction _ _
      _ = c := B.residuePart_pad c
  · rintro ⟨a,q⟩
    obtain ⟨w,rfl⟩ := W.mkQ_surjective q
    let x := A.padResidue a + actRows A.rows w
    refine ⟨B.residuePart x,(reduce x).trans (Prod.ext ?_ ?_)⟩
    · exact (A.residuePart_direction _ _).trans (A.residuePart_pad a)
    · change W.mkQ (A.padResidue a ∘ A.free + actRows A.rows w ∘ A.free) = _
      rw [A.pad_free,A.direction_free,zero_add]

end ValueFrame
end GeneralizedEuler.Section4
