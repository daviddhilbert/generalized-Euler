module

public import Section4.SpecializedConePartitions
public import Section4.StrictConePartition
import all Section4.SpecializedConePartitions
import all Section4.FiniteSignSpecialization
import all Section4.StrictConePartition
import all Section4.LinearSignTransfer
import all Section4.ParameterConeDirections
import all Section4.ProjectedConeRays
import all Section4.AdaptedParameterCones
import all Section4.PolyhedralProjectionTests

/-! Partition at the actual base parameters of a mixed homogeneous system.
The unrestricted coordinates vary in the ordered value space. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open Set

variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {X Y U W : Type*}

omit [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem Transfers.pull {s : (V →ₗ[F] F) → X → Y} {r : (V →ₗ[F] F) → U → W}
    {P : X → Prop} {Q : Y → Prop} (h : Transfers s P Q) (g : U → X) (k : W → Y)
    (law : ∀ f x, s f (g x)=k (r f x)) : Transfers r (fun x => P (g x)) (fun y => Q (k y)) := by
  intro x
  obtain ⟨v,hv⟩ := h (g x)
  exact ⟨v,fun f sf => (hv f sf).trans (Iff.of_eq (congrArg Q (law f x)))⟩

variable {I B J : Type} [Fintype I] [Fintype B] [Fintype J]
abbrev PairSpace (I B : Type) (A : Type*) := (I → A) × (B → A)

def valueMixed (a : J → PairSpace I B F →ₗ[F] F) (strict : J → Prop) (u : PairSpace I B V) :=
  ∀ i, let v := evalRow ((a i).comp packLinear.symm.toLinearMap) (pack u.1 u.2)
       0≤v ∧ (strict i → 0<v)

def specPair (f : V →ₗ[F] F) (x : PairSpace I B V) : PairSpace I B F :=
  (fun i => f (x.1 i),fun i => f (x.2 i))

omit [IsStrictOrderedRing F] [IsStrictOrderedModule F V] [IsOrderedAddMonoid V] in
theorem mixed_transfers (a : J → PairSpace I B F →ₗ[F] F) (strict : J → Prop) :
    Transfers (specPair (V := V)) (valueMixed a strict) (MixedCone a strict) := by
  classical
  intro x
  let w i := evalRow ((a i).comp packLinear.symm.toLinearMap) (pack x.1 x.2)
  refine ⟨Finset.univ.image w,fun f sign => ?_⟩
  have h (i) : SameSign (w i) (a i (specPair f x)) := by
    have eq := specialize_row ((a i).comp packLinear.symm.toLinearMap) f (pack x.1 x.2)
    exact eq ▸ sign _ (Finset.mem_image_of_mem w (Finset.mem_univ i))
  constructor
  · intro law
    exact ⟨fun i => (h i).1.mp (law i).1,fun i hi =>
      (lt_iff_lt_of_le_iff_le' (h i).2 (h i).1).mp ((law i).2 hi)⟩
  · intro law i
    exact ⟨(h i).1.mpr (law.1 i),fun hi => (lt_iff_lt_of_le_iff_le' (h i).2 (h i).1).mpr (law.2 i hi)⟩

omit [IsStrictOrderedRing F] [IsStrictOrderedModule F V] [IsOrderedAddMonoid V] in
theorem packed_transfers (d : SimpleCone F (PairSpace I B F)) :
    Transfers specPair (fun u : PairSpace I B V => pack u.1 u.2 ∈ d.packed.valuePart) (fun u => u∈d.openPart) := by
  intro x
  obtain ⟨s,hs⟩ := d.packed.transfers_open (pack x.1 x.2)
  refine ⟨s,fun f h => (hs f h).trans ?_⟩
  convert d.mem_packed (fun i => f (x.1 i)) (fun j => f (x.2 j)) using 2
  · funext i; cases i <;> rfl
  · rfl

variable (a : J → PairSpace I B F →ₗ[F] F) (pointed : ∀ w, (∀ i, a i w=0) → w=0) (strict : J → Prop)

include pointed in
theorem value_mixed_partition (G : Submodule F V) (p : B → G) :
    ∃ (r : ℕ) (t : Fin r → G) (_ : ∀ j, 0<(t j : V))
      (n : ℕ) (d : Fin n → SimpleCone F (PairSpace I (Fin r) F)),
      (∀ t j, (∀ b, 0≤((d t).ray j).2 b) ∧
        ∀ i h, 0<((d t).ray j).2 i → 0<((d t).ray j).2 h → i=h) ∧
      Pairwise (fun i j => Disjoint {x : I → V | pack x (fun j => (t j : V)) ∈ (d i).packed.valuePart}
        {x | pack x (fun j => (t j : V)) ∈ (d j).packed.valuePart}) ∧
      ∀ x, (∃ i, pack x (fun j => (t j : V)) ∈ (d i).packed.valuePart) ↔ valueMixed a strict (x,fun j => p j) := by
  classical
  obtain ⟨forms,adapted⟩ := all_face_tests a pointed (LinearMap.snd _ _ _)
  obtain ⟨_,cs,compat,cover⟩ := parameter_cover forms
  obtain ⟨s,hs⟩ := value_cover cs cover (fun j => (p j : V))
  let c := cs s
  let t j : G := ⟨extendMatrix c.param.leftInverse (fun j => (p j : V)) j,
    extendMatrix_old G _ _ (fun j => (p j).property) j⟩
  obtain ⟨positive,rec⟩ := c.mem_valuePart _ |>.mp hs
  obtain ⟨n,d,support,dj,cov⟩ := mixed_fiber_partition a pointed strict c (compat s) adapted
  let g (x : PairSpace I (Fin c.rays) V) : PairSpace I B V := (x.1,extendMatrix c.param x.2)
  have mixed := (mixed_transfers (V := V) a strict).pull (r := specPair) g (overParameter c) (by
    intro f x; exact Prod.ext rfl (specialize_matrix f c.param x.2))
  have nonneg : Transfers (specPair (F := F)) (fun u : PairSpace I (Fin c.rays) V => ∀ j, 0≤u.2 j)
      (fun u => ∀ j, 0≤u.2 j) := by
    intro x
    exact ⟨Finset.univ.image x.2,fun f h => forall_congr' fun j =>
      (h _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))).1⟩
  have rhs := mixed.binary And nonneg
  have lhs := Transfers.finite (fun p => ∃ i, p i) (fun i => packed_transfers (V := V) (d i))
  refine ⟨_,t,positive,n,d,support,fun i j ne => Set.disjoint_left.mpr (fun {x} hi hj => ?_),fun x => ?_⟩
  · have tr := (packed_transfers (V := V) (d i)).binary (fun p q => p → q → False) (packed_transfers (d j))
    exact tr.universal (fun _ hy => Set.disjoint_left.mp (dj ne) hy) (x,fun j => (t j : V)) hi hj
  · have eq := (lhs.binary Iff rhs).universal cov (x,fun j => (t j : V))
    have ident : g (x,fun j => (t j : V)) = (x,fun j => (p j : V)) := Prod.ext rfl rec
    exact eq.trans ⟨fun h => ident ▸ h.1,fun h => ⟨ident.symm ▸ h,fun j => (positive j).le⟩⟩

end GeneralizedEuler.Section4.Polyhedral
