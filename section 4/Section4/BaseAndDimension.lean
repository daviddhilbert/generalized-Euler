module

public import Section4.Objects
public import Section2.SortedQuantifierBlock

public section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder

universe z
variable {L : Language} {E : Type*} {Z : TCsort → Type z}

/-- The fixed-base witness of 4.1. The elementary extension of the base
inside the ambient structure may enlarge VF while keeping its RV sort. -/
theorem rv_base_witness (M : SortedStructure L E Z) (S N : SortedSubstructure M)
    (inc : ∀ s, S.carrier s ⊆ N.carrier s) (same : N.carrier .rv ⊆ S.carrier .rv)
    (elementary : ∀ {Var : TCsort → Type z} (φ : SortedFormula L E Var)
      (a : ∀ s, Var s → N.carrier s),
      φ.realize N.structureOn a ↔ φ.realize M (fun s => Subtype.val ∘ a s))
    {n : ℕ} {U : Set (Fin n → Z .rv)} (hd : isRVSet M S U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i, x i ∈ S.carrier .rv := by
  obtain ⟨φ,hφ⟩ := hd
  let params (s : TCsort) (t : S.carrier s) : N.carrier s := ⟨t.val,inc s t.property⟩
  let rename (s : TCsort) : (S.carrier s ⊕ RVVariables (Fin n) s) →
      AddSortedBlock (fun t => (S.carrier t : Type _)) .rv n s :=
    Sum.map id (by cases s; exacts [PEmpty.elim, fun i => ⟨i,⟨rfl⟩⟩])
  let θ := φ.relabel rename
  have spec (x : Fin n → Z .rv) :
      θ.realize M (appendSortedBlock (fun _ => Subtype.val) x) ↔ x ∈ U := by
    let a : ∀ s, RVVariables (Fin n) s → Z s
      | .rv => x
      | .vf => PEmpty.elim
    have hh := (hφ a).symm
    rw [SortedFormula.realize_relabel]
    convert hh using 2
    · funext s i
      cases s <;> rcases i with i | i <;> first | rfl | exact i.elim
    · rfl
  obtain ⟨x,hx⟩ := hne
  have ex := (θ.realize_exBlock M .rv _).mpr ⟨x,(spec x).mpr hx⟩
  obtain ⟨y,hy⟩ := (θ.realize_exBlock N.structureOn .rv _).mp
    ((elementary (θ.exBlock .rv n) params).mpr ex)
  refine ⟨fun i => (y i).val, (spec _).mp ?_, fun i => same (y i).property⟩
  have lift := (elementary θ (appendSortedBlock params y)).mp hy
  have eq : appendSortedBlock (fun _ => Subtype.val) (fun i => (y i).val) =
      (fun s => Subtype.val ∘ appendSortedBlock params y s) := by
    funext s i
    rcases i with i | ⟨i,⟨he⟩⟩
    · rfl
    · cases he; rfl
  rw [eq]; exact lift

section Dimension
variable {A B X Y : Type*}
variable (P : A → Set X) (Q : B → Set Y)

/-- Fixed input field tuple. Its RV-fiber splits by the finitely many
output field tuples occurring under the mixed bijection. -/
def mixedSlice (f : (Σ a, P a) → Σ b, Q b) (a : A) (b : B) : Set X :=
  {x | ∃ hx : x ∈ P a, (f ⟨a,⟨x,hx⟩⟩).1 = b}

theorem mixed_fiber_partition (f : (Σ a, P a) → Σ b, Q b) (a : A)
    (F : Finset B) (cover : ∀ x : P a, (f ⟨a,x⟩).1 ∈ F) :
    P a = ⋃ b ∈ F, mixedSlice P Q f a b := by
  ext x
  simp only [Set.mem_iUnion,mixedSlice,Set.mem_ofPred_eq, exists_prop]
  exact ⟨fun hx => ⟨_,cover ⟨x,hx⟩,hx,rfl⟩,fun ⟨_,_,hx,_⟩ => hx⟩

/-- The dimension comparison for 4.2. The two dimension inputs are the
finite union law and monotonicity under the definable fiber embeddings. -/
theorem fiber_dimension_le {D : Type*} [Preorder D] (d : D)
    (dimX : Set X → D) (dimY : Set Y → D) (f : (Σ a, P a) ≃ Σ b, Q b)
    (finiteImage : ∀ a, (Set.range fun x : P a => (f ⟨a,x⟩).1).Finite)
    (unionLaw : ∀ (F : Finset B) (U : B → Set X), (∀ b ∈ F, dimX (U b) ≤ d) →
      dimX (⋃ b ∈ F, U b) ≤ d)
    (embed : ∀ a b, dimX (mixedSlice P Q f a b) ≤ dimY (Q b))
    (bound : ∀ b, dimY (Q b) ≤ d) : ∀ a, dimX (P a) ≤ d := by
  intro a
  classical
  let F := (finiteImage a).toFinset
  rw [mixed_fiber_partition P Q f a F (fun x => (finiteImage a).mem_toFinset.mpr ⟨x,rfl⟩)]
  exact unionLaw F _ fun b _ => (embed a b).trans (bound b)

end Dimension
end GeneralizedEuler.Section4
