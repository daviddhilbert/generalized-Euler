module

public import Section4.SimplicialValueFibers
import all Section4.SimplicialValueFibers

/-! Grouping projected rays into the free vertical coefficients and the
nonempty blocks over parameter rays. Removing one coordinate per block
preserves the original degree after padding. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [LinearOrder V]
  {k r n : ℕ}

def optionBlocks {B : Type*} (T : Option B → Type*) : T none ⊕ ((b : B) × T (some b)) ≃ ((b : Option B) × T b) where
  toFun := Sum.elim (fun x => ⟨none,x⟩) (fun x => ⟨some x.1,x.2⟩)
  invFun x := match x with | ⟨none,t⟩ => .inl t | ⟨some j,t⟩ => .inr ⟨j,t⟩
  left_inv x := by rcases x with x|⟨j,x⟩ <;> rfl
  right_inv x := by rcases x with ⟨_|j,x⟩ <;> rfl

theorem build_ray_layout (group : Fin n → Option (Fin r)) (hit : ∀ b, ∃ j, group j=some b)
    (bound : n ≤ k+r) (G : Submodule F V) (t : Fin r → G) (positive : ∀ b, 0<(t b : V)) :
    ∃ (c : ConeFiber G k) (e : c.Coeff ≃ Fin n) (h : Fin c.groups ≃ Fin r),
      (∀ b, c.width b=t (h b)) ∧
      (∀ i, group (e (.inl i))=none) ∧ (∀ b j, group (e (.inr ⟨b,j⟩))=some (h b)) := by
  classical
  let T (b : Option (Fin r)) := {j : Fin n // group j=b}
  let v := Fintype.card (T none)
  let dim (b : Fin r) := Fintype.card (T (some b))-1
  have sz (b) : dim b+1 = Fintype.card (T (some b)) := by
    obtain ⟨j,hj⟩ := hit b
    have pos := Fintype.card_pos_iff.mpr (show Nonempty (T (some b)) from ⟨⟨j,hj⟩⟩)
    dsimp [dim]; omega
  let vert : Fin v ≃ T none := (Fintype.equivFin _).symm
  let block (b) : Fin (dim b+1) ≃ T (some b) := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using sz b)
  let e := (Equiv.sumCongr vert (Equiv.sigmaCongrRight block)).trans ((optionBlocks T).trans (Equiv.sigmaFiberEquiv group))
  have total : v + (∑ b, dim b) + r = n := by
    have eq := Fintype.card_congr e
    simpa [Fintype.card_sigma,Finset.sum_add_distrib,Nat.add_assoc] using eq
  let pad := k-(v+∑ b, dim b)
  have size : k = pad + (v+∑ b, dim b) := by dsimp [pad]; omega
  let layout : Fin k ≃ Fin pad ⊕ (Fin v ⊕ ((b : Fin r) × Fin (dim b))) :=
    Fintype.equivOfCardEq (by simpa [Fintype.card_sigma] using size)
  let c : ConeFiber G k := ⟨v,r,dim,t,positive,pad,layout⟩
  exact ⟨c,e,Equiv.refl _,fun _ => rfl,fun i => (vert i).property,fun b j => (block b j).property⟩

end GeneralizedEuler.Section4.Polyhedral
