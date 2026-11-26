module

public import Section4.ValueStratification
public import Section4.CellProducts
import all Section4.CellProducts
import all Section4.ValueFrames

/-! Extract the rectangle on an independent affine piece from the separated
formula in split coordinates. The linear section only enters the proof and
the representatives of base intercepts. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T] [AddCommGroup V] [Module F V]
  (v : T →ₗ[F] V) (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id) {G : Submodule F V}
  {n r : ℕ}

namespace ValueFrame
variable (A : ValueFrame G r n)

abbrev dependent := {i : Fin n // i ∉ Set.range A.free}

def extendResidues (b : A.dependent → v.ker) (i : Fin n) : v.ker := by
  classical exact if h : i ∉ Set.range A.free then b ⟨i,h⟩ else 0

theorem extend_free (b : A.dependent → v.ker) (i : Fin r) :
    A.extendResidues v b (A.free i) = 0 := by simp [extendResidues]

theorem extend_dependent (b : A.dependent → v.ker) (i : A.dependent) :
    A.extendResidues v b i.val = b i := by simp [extendResidues,i.property]

def lift (z : Fin r → T) : Fin n → T :=
  actRows A.rows z + fun i => s (A.shift i).val

def assemble (z : Fin r → T) (b : A.dependent → v.ker) : Fin n → T :=
  A.lift s z + fun i => (A.extendResidues v b i).val

theorem assemble_free (z : Fin r → T) (b : A.dependent → v.ker) :
    A.assemble v s z b ∘ A.free = z := by
  funext i
  simp [assemble,lift,actRows,A.freeRow,A.freeShift,ite_smul,A.extend_free]

include hs

theorem assemble_value (z : Fin r → T) (b : A.dependent → v.ker) :
    v ∘ A.assemble v s z b = A.eval (v ∘ z) := by
  funext i
  change v (actRows A.rows z i + s _ + _) = _ + _
  rw [map_add,map_add,(A.extendResidues v b i).property,add_zero,
    show v (s (A.shift i).val) = _ from DFunLike.congr_fun hs _]
  exact congrArg (· + (A.shift i).val) (congrFun (actRows_map v A.rows z) i)

theorem lift_units (α : Fin r → V) (a : Fin r → v.ker) (b : A.dependent → v.ker) :
    splitUnit v s hs ∘ A.assemble v s (fun i => s (α i) + (a i).val) b =
      actRows A.rows a + A.extendResidues v b := by
  let z (i) := s (α i) + (a i).val
  have hz : v ∘ z = α := funext fun i => by
    change v (_ + _) = _
    rw [map_add,(a i).property,add_zero]; exact DFunLike.congr_fun hs _
  have hv := A.assemble_value v s hs z b
  rw [hz] at hv
  funext i
  apply Subtype.ext
  change actRows A.rows z i + s _ + _ - s (v (A.assemble v s z b i)) = _
  rw [show v (A.assemble v s z b i) = A.eval α i from congrFun hv i]
  have ha := congrFun (actRows_map v.ker.subtype A.rows a) i
  have hα := congrFun (actRows_map s A.rows α) i
  change _ = (actRows A.rows a i).val + _
  rw [show (actRows A.rows a i).val = _ from ha]
  simp only [eval,Pi.add_apply,map_add]
  rw [show s (actRows A.rows α i) = _ from hα]
  simp [actRows,z,smul_add,Finset.sum_add_distrib]
  abel

theorem shear_assemble (L : (V ⧸ G) →ₗ[F] v.ker) (z : Fin r → T) (b : A.dependent → v.ker) :
    shear v G L ∘ A.assemble v s z b = A.assemble v s (shear v G L ∘ z) b := by
  let g := shear v G L
  have base (i : Fin n) : g (s (A.shift i).val) = s (A.shift i).val := by
    apply shear_fixes_base
    rw [show v (s (A.shift i).val) = (A.shift i).val from DFunLike.congr_fun hs _]
    exact (A.shift i).property
  funext i
  change g (actRows A.rows z i + s _ + _) = _ + _ + _
  rw [map_add,map_add,base,show g (A.extendResidues v b i).val = _ from
    shear_fixes_base v G L ((A.extendResidues v b i).property ▸ G.zero_mem)]
  exact congrArg (fun x => x + s (A.shift i).val + (A.extendResidues v b i).val)
    (congrFun (actRows_map g.toLinearMap A.rows z) i)

theorem rectangle_test (D : Set (Fin r → V)) (α : Fin r → V) (ha : α ∈ D)
    (hi : LinearIndependent F (G.mkQ ∘ α)) (U : Set (Fin n → T))
    (inv : ∀ L x, x ∈ U → shear v G L ∘ x ∈ U)
    (R : Set (Fin n → v.ker))
    (cell : ∀ x, v ∘ x ∈ A.eval '' D → (x ∈ U ↔ splitUnit v s hs ∘ x ∈ R))
    (z : Fin r → T) (hz : v ∘ z ∈ D) (b : A.dependent → v.ker) :
    A.assemble v s z b ∈ U ↔ A.extendResidues v b ∈ R := by
  have transport (a c : Fin r → v.ker) :
      actRows A.rows a + A.extendResidues v b ∈ R → actRows A.rows c + A.extendResidues v b ∈ R := by
    let t (a : Fin r → v.ker) i := s (α i) + (a i).val
    have tv (a : Fin r → v.ker) : v ∘ t a = α := funext fun i => by
      change v (_ + _) = _
      rw [map_add,(a i).property,add_zero]; exact DFunLike.congr_fun hs _
    have test (a : Fin r → v.ker) : A.assemble v s (t a) b ∈ U ↔
        actRows A.rows a + A.extendResidues v b ∈ R := by
      rw [cell _ ⟨α,ha,by rw [A.assemble_value v s hs,tv]⟩,A.lift_units v s hs α a b]
    obtain ⟨L,hL⟩ := transitive_independent_fiber v G (t a) (t c) ((tv a).symm ▸ hi)
      ((tv a).trans (tv c).symm)
    intro hr
    have h := inv L _ ((test a).mpr hr)
    rwa [A.shear_assemble v s hs,hL,test c] at h
  let a := splitUnit v s hs ∘ z
  have reconstruct : (fun i => s ((v ∘ z) i) + (a i).val) = z := by
    funext i; change s (v (z i)) + (z i - s (v (z i))) = z i; abel
  have units := A.lift_units v s hs (v ∘ z) a b
  rw [reconstruct] at units
  rw [cell _ ⟨_,hz,(A.assemble_value v s hs z b).symm⟩,units]
  have equal := Iff.intro (transport a 0) (transport 0 a)
  have zero : actRows A.rows (0 : Fin r → v.ker) = 0 := by funext i; simp [actRows]
  simpa only [zero,zero_add] using equal

/-- Normalize an arbitrary tuple whose values lie on the frame. -/
def normalize (x : Fin n → T) (hx : v ∘ x = A.eval ((v ∘ x) ∘ A.free))
    (i : A.dependent) : v.ker :=
  ⟨x i.val - A.lift s (x ∘ A.free) i.val, by
    change v (_ - (_ + s _)) = 0
    rw [map_sub,map_add,show v (s (A.shift i.val).val) = _ from DFunLike.congr_fun hs _,
      show v (actRows A.rows (x ∘ A.free) i.val) = _ from congrFun (actRows_map v A.rows _) i.val]
    exact sub_eq_zero.mpr (congrFun hx i.val)⟩

theorem assemble_normalize (x : Fin n → T) (hx : v ∘ x = A.eval ((v ∘ x) ∘ A.free)) :
    A.assemble v s (x ∘ A.free) (A.normalize v s hs x hx) = x := by
  funext i
  by_cases hi : i ∈ Set.range A.free
  · obtain ⟨j,rfl⟩ := hi
    exact congrFun (A.assemble_free v s (x ∘ A.free) _) j
  · let j : A.dependent := ⟨i,hi⟩
    change A.lift s _ i + (A.extendResidues v _ j.val).val = _
    rw [A.extend_dependent]
    change A.lift s _ i + (x i - A.lift s _ i) = _
    abel

omit hs in
theorem assemble_injective :
    Function.Injective (fun p : (Fin r → T) × (A.dependent → v.ker) => A.assemble v s p.1 p.2) := by
  rintro ⟨z,b⟩ ⟨w,c⟩ h
  have free := congrArg (fun x : Fin n → T => x ∘ A.free) h
  change A.assemble v s z b ∘ A.free = A.assemble v s w c ∘ A.free at free
  rw [A.assemble_free,A.assemble_free] at free
  subst w
  refine Prod.ext (by rfl) ?_
  funext i; apply Subtype.ext
  have he := congrFun h i.val
  change A.lift s z i.val + (A.extendResidues v b i.val).val =
    A.lift s z i.val + (A.extendResidues v c i.val).val at he
  rw [A.extend_dependent,A.extend_dependent] at he
  exact add_left_cancel he

/-- The actual equivalence of the chart piece and its rectangle. Its free
dimension is the rank of the value projection. -/
def rectangleEquiv (D : Set (Fin r → V)) (α : Fin r → V) (ha : α ∈ D)
    (hi : LinearIndependent F (G.mkQ ∘ α)) (U : Set (Fin n → T))
    (inv : ∀ L x, x ∈ U → shear v G L ∘ x ∈ U) (R : Set (Fin n → v.ker))
    (cell : ∀ x, v ∘ x ∈ A.eval '' D → (x ∈ U ↔ splitUnit v s hs ∘ x ∈ R)) :
    ({z : Fin r → T // v ∘ z ∈ D} × {b // A.extendResidues v b ∈ R}) ≃
      {x : Fin n → T // x ∈ U ∧ v ∘ x ∈ A.eval '' D} := by
  let f (p : {z : Fin r → T // v ∘ z ∈ D} × {b // A.extendResidues v b ∈ R}) :
      {x : Fin n → T // x ∈ U ∧ v ∘ x ∈ A.eval '' D} :=
    ⟨A.assemble v s p.1.val p.2.val,
      (A.rectangle_test v s hs D α ha hi U inv R cell _ p.1.property _).mpr p.2.property,
      _,p.1.property,(A.assemble_value v s hs _ _).symm⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q eq
    have h := A.assemble_injective v s (a₁ := (p.1.val,p.2.val)) (a₂ := (q.1.val,q.2.val))
      (congrArg Subtype.val eq)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  · rintro ⟨x,hu,γ,hγ,eq⟩
    let z := x ∘ A.free
    have hvz : v ∘ z = γ := by
      change (v ∘ x) ∘ A.free = γ
      rw [← eq,A.project_eval]
    have hx : v ∘ x = A.eval ((v ∘ x) ∘ A.free) := by
      change v ∘ x = A.eval (v ∘ z); rw [hvz]; exact eq.symm
    let b := A.normalize v s hs x hx
    have he : A.assemble v s z b = x := A.assemble_normalize v s hs x hx
    have hz : v ∘ z ∈ D := hvz.symm ▸ hγ
    exact ⟨(⟨z,hz⟩,⟨b,(A.rectangle_test v s hs D α ha hi U inv R cell z hz b).mp (he.symm ▸ hu)⟩),
      Subtype.ext he⟩

end ValueFrame
end GeneralizedEuler.Section4
