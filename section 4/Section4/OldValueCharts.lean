module

public import Section4.CanonicalChartCover
public import Section4.ResidueBaseValues
import all Section4.SliceComparison
import all Section4.PositiveRectangles
import all Section4.ValueStratification
import all Section4.CanonicalChartMaps
import all Section4.FiberMatching
import all Section2.RVVectorSpace

/-! A nonempty positive chart supported on old values has rank zero.
Consequently a positive definable image fixed by all base shears has only
finitely many value tuples. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2
variable {F V T : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup T] [Module F T]
  (v : T →ₗ[F] V) (G : Submodule F V)

theorem old_value_of_fixed (d : v.ker) (hd : d ≠ 0) (x : T)
    (fixed : ∀ L, shear v G L x = x) : v x ∈ G := by
  by_contra outside
  have notzero : G.mkQ (v x) ∉ (⊥ : Submodule F (V ⧸ G)) := fun h => outside ((Submodule.Quotient.mk_eq_zero G).mp h)
  obtain ⟨f,hf,_⟩ := Submodule.exists_le_ker_of_notMem notzero
  have eq := fixed (f.smulRight d)
  change x + ((f (G.mkQ (v x))) • d).val = x at eq
  exact (smul_ne_zero hf hd) (Subtype.ext (show ((f (G.mkQ (v x))) • d).val = (0 : T) by simpa only [add_eq_left] using eq))

variable (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id) {J : Language} [J.Structure V] {n : ℕ}

include hs in
theorem rank_zero_of_old_chart (a : ChartPiece v G J n) (nonempty : a.residue.Nonempty)
    (old : ∀ x ∈ a.carrier s, ∀ j, v (x j) ∈ G) : a.value.rank = 0 := by
  obtain ⟨γ,hγ,ind⟩ := a.value.independent
  let z := s ∘ γ
  have eq : v ∘ z = γ := funext fun j => DFunLike.congr_fun hs (γ j)
  let A := a.value.frame
  let b := nonempty.choose
  let x := A.assemble v s z b
  have hit : x ∈ a.carrier s := (a.assemble_mem (v := v) s _ (eq.symm ▸ hγ) b).mpr nonempty.choose_spec
  by_contra h
  let j : Fin a.value.rank := ⟨0,Nat.pos_of_ne_zero h⟩
  have hj := old x hit (A.free j)
  have read : x (A.free j) = z j := congrFun (A.assemble_free v s z b) j
  rw [read,show v (z j) = γ j from congrFun eq j] at hj
  exact ind.ne_zero j ((Submodule.Quotient.mk_eq_zero G).mpr hj)

include hs in
theorem finite_values_of_old_charts {l} (p : Fin l → ChartPiece v G J n) (D : Set (Fin n → T))
    (ne : ∀ i, (p i).residue.Nonempty) (cv : (⋃ i, (p i).carrier s) = D)
    (old : ∀ x ∈ D, ∀ j, v (x j) ∈ G) : ((fun x => v ∘ x) '' D).Finite := by
  have fin i : (p i).value.support.Finite := by
    have rank := rank_zero_of_old_chart v G s hs (p i) (ne i) (fun x hx => old x (cv ▸ Set.mem_iUnion.mpr ⟨i,hx⟩))
    have e : Fin (p i).value.rank ≃ Fin 0 := finCongr rank
    let : IsEmpty (Fin (p i).value.rank) := ⟨fun j => (e j).elim0⟩
    exact (Set.toFinite (p i).value.domain).image _
  apply (Set.finite_iUnion fin).subset
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (cv.symm ▸ hx)
  exact Set.mem_iUnion.mpr ⟨i,(p i).value_mem s hs hi⟩

end GeneralizedEuler.Section4
