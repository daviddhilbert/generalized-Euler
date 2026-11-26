module

public import Section4.RelativeResidues
import all Section4.RelativeResidues

/-! The quotient in the residue refinement has exactly one unrestricted
positive residue coordinate for each unit of lost value rank. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open scoped Matrix
variable {F T : Type*} [Field F] [AddCommGroup T] [Module F T] {r k : ℕ}

def unitColumns (j : Fin k ↪ Fin r) : Matrix (Fin r) (Fin k) F :=
  fun i c => if j c = i then 1 else 0

theorem unitColumns_free (j : Fin k ↪ Fin r) (x : Fin k → T) :
    actRows (unitColumns (F := F) j) x ∘ j = x := by
  classical funext i; simp [actRows,unitColumns,j.injective.eq_iff,ite_smul]

theorem rows_scalar (A : Matrix (Fin r) (Fin k) F) (x : Fin k → F) :
    actRows A x = A.mulVecLin x := rfl

/-- The complementary coordinates are read after an invertible scalar
matrix change. The inverse pads them with zeros and returns to the old
coordinates. Both directions use just linear forms. -/
def quotientCoordinates (C : Matrix (Fin r) (Fin k) F) (inj : Function.Injective C.mulVecLin)
    (j : Fin k ↪ Fin r) :
    ((Fin r → T) ⧸ LinearMap.range (rowsLinear (T := T) C)) ≃
      ({i : Fin r // i ∉ Set.range j} → T) := by
  classical
  let P : Matrix (Fin r) (Fin k) F := unitColumns j
  have pinj : Function.Injective P.mulVecLin := by
    intro x y eq
    change actRows P x = actRows P y at eq
    simpa only [P,unitColumns_free] using congrArg (fun z : Fin r → F => z ∘ j) eq
  let U := (ambient_coordinate_change P C pinj inj).choose
  have hU := (ambient_coordinate_change P C pinj inj).choose_spec
  let W := LinearMap.range (rowsLinear (T := T) C)
  let zeroPad (b : {i : Fin r // i ∉ Set.range j} → T) (i : Fin r) :=
    if h : i ∉ Set.range j then b ⟨i,h⟩ else 0
  let extract (x : Fin r → T) (i : {i : Fin r // i ∉ Set.range j}) := actRows U.inv x i.val
  have undo (x : Fin r → T) : actRows U.inv (actRows U.val x) = x := by
    rw [← actRows_mul,U.inv_val,actRows_one]
  have cancels (x : Fin k → T) (i : {i : Fin r // i ∉ Set.range j}) : actRows P x i.val = 0 := by
    have ne (k : Fin _) : j k ≠ i.val := fun h => i.property ⟨k,h⟩
    simp [P,actRows,unitColumns,ne]
  let lin : (Fin r → T) →ₗ[F] ({i : Fin r // i ∉ Set.range j} → T) :=
    (LinearMap.funLeft F T (fun i : {i : Fin r // i ∉ Set.range j} => i.val)).comp (rowsLinear U.inv)
  have kill : W ≤ LinearMap.ker lin := by
    rintro _ ⟨x,rfl⟩
    change extract (actRows C x) = 0
    change (fun i : {i : Fin r // i ∉ Set.range j} => actRows U.inv (actRows C x) i.val) = 0
    rw [← hU,actRows_mul,undo]; exact funext (cancels x)
  let read := W.liftQ lin kill
  let write (b : {i : Fin r // i ∉ Set.range j} → T) := W.mkQ (actRows U.val (zeroPad b))
  refine ⟨read,write,?_,?_⟩
  · intro q
    obtain ⟨x,rfl⟩ := W.mkQ_surjective q
    change W.mkQ (actRows U.val (zeroPad (extract x))) = W.mkQ x
    apply sub_eq_zero.mp; rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero W).mpr
    let y := actRows U.inv x
    refine ⟨fun a => - y (j a),?_⟩
    have eq : actRows P (fun a => - y (j a)) = zeroPad (extract x) - y := by
      funext i
      by_cases hi : i ∈ Set.range j
      · obtain ⟨a,rfl⟩ := hi
        exact (congrFun (unitColumns_free (F := F) j (fun a => -y (j a))) a).trans
          (by simp [zeroPad])
      · change actRows P _ i = (if h : i ∉ Set.range j then extract x ⟨i,h⟩ else 0) - y i
        rw [dite_eq_left hi,show extract x ⟨i,hi⟩ = y i from rfl,sub_self]
        exact cancels _ ⟨i,hi⟩
    change actRows C _ = _
    rw [← hU,actRows_mul,eq]
    rw [show actRows U.val (zeroPad (extract x) - y) = _ from (rowsLinear (T := T) U.val).map_sub _ _]
    change _ - actRows U.val (actRows U.inv x) = _
    rw [← actRows_mul,U.val_inv,actRows_one]; rfl
  · intro b
    change extract (actRows U.val (zeroPad b)) = b
    funext i
    change actRows U.inv (actRows U.val (zeroPad b)) i.val = _
    rw [undo]; exact dite_eq_left i.property

theorem complement_count (j : Fin k ↪ Fin r) : Fintype.card {i : Fin r // i ∉ Set.range j} = r-k := by
  classical
  change Fintype.card ((Set.range j)ᶜ : Set (Fin r)) = _
  rw [Fintype.card_compl_set,← Fintype.card_congr (Equiv.ofInjective j j.injective)]
  simp

namespace ValueFrame
variable {V : Type*} [AddCommGroup V] [Module F V] {G : Submodule F V} {n : ℕ}
  (A : ValueFrame G r n) (B : ValueFrame G k n)

theorem refinement_injective (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) : Function.Injective (A.projectedRows B).mulVecLin := by
  obtain ⟨he,_⟩ := A.refinement_equations B α hi h
  intro x y e
  have eq : actRows B.rows x = actRows B.rows y := by
    rw [he,actRows_mul,actRows_mul]; exact congrArg (actRows A.rows) e
  exact (B.direction_free x).symm.trans ((congrArg (fun t : Fin n → F => t ∘ B.free) eq).trans
    (B.direction_free y))

/-- The first component of this bijection is the old residue projection.
Thus every definable subdivision of the old residues pulls back with the
same unrestricted factor of the precise lost ambient degree. -/
theorem restricted_refinement (α : Fin k → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (h : B.eval α ∈ Set.range A.eval) (D : Set (A.dependent → T)) :
    ∃ e : {b : B.dependent → T // A.residuePart (B.padResidue b) ∈ D} ≃
      D × (Fin (r-k) → T), ∀ b, (e b).1.val = A.residuePart (B.padResidue b.val) := by
  classical
  let C := A.projectedRows B
  have eq := (A.refinement_equations B α hi h).1
  let j : Fin k ↪ Fin r := Fin.castLEEmb (A.refinement_rank B α hi h)
  let rem := Fintype.equivFinOfCardEq (complement_count j)
  let q := quotientCoordinates (T := T) C (A.refinement_injective B α hi h) j
  let e := (A.relativeResidueEquiv B C eq).trans
    (Equiv.prodCongr (Equiv.refl _) (q.trans (Equiv.arrowCongr rem (Equiv.refl T))))
  have fst (b) : (e b).1 = A.residuePart (B.padResidue b) := rfl
  let f (b : {b : B.dependent → T // A.residuePart (B.padResidue b) ∈ D}) :
      D × (Fin (r-k) → T) := (⟨(e b.val).1,fst b.val ▸ b.property⟩,(e b.val).2)
  refine ⟨Equiv.ofBijective f ⟨?_,?_⟩,fun b => fst b.val⟩
  · intro b c he; apply Subtype.ext; apply e.injective
    exact Prod.ext (congrArg (fun z : D × (Fin (r-k) → T) => z.1.val) he) (congrArg (fun z : D × (Fin (r-k) → T) => z.2) he)
  · rintro ⟨b,t⟩
    let x := e.symm (b.val,t)
    have ex : e x = (b.val,t) := e.apply_symm_apply _
    have dx : A.residuePart (B.padResidue x) ∈ D := by rw [← fst,ex]; exact b.property
    exact ⟨⟨x,dx⟩,Prod.ext (Subtype.ext (congrArg Prod.fst ex)) (congrArg (fun z : (A.dependent → T) × (Fin (r-k) → T) => z.2) ex)⟩

end ValueFrame
end GeneralizedEuler.Section4
