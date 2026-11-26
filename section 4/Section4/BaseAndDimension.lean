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

/-- Restriction of the bijection to one pair of field tuples gives an
embedding of RV sets. The output fiber is fixed in this construction. -/
def sliceEmbedding (f : (Σ a, P a) ≃ Σ b, Q b) (a : A) (b : B) :
    mixedSlice P Q f a b ↪ Q b := by
  let pre (x : mixedSlice P Q f a b) : Σ a, P a := ⟨a,⟨x.val,x.property.choose⟩⟩
  have tag (x) : (f (pre x)).1 = b := x.property.choose_spec
  let out (x) : Q b := (tag x) ▸ (f (pre x)).2
  have eq (x) : f (pre x) = ⟨b,out x⟩ := Sigma.ext (tag x) (by simp [out])
  refine ⟨out,fun {x y} he => ?_⟩
  have h : pre x = pre y := f.injective ((eq x).trans ((congrArg (Sigma.mk b) he).trans (eq y).symm))
  exact Subtype.ext (congrArg (fun p : Σ a, P a => p.2.val) h)

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

/-- Lemma 4.2. The least upper bounds describing the two fiber dimensions
coincide, also when one of the indexing families is empty. -/
theorem fiber_dimension_eq {D : Type*} [PartialOrder D] (d d' : D)
    (dimX : Set X → D) (dimY : Set Y → D) (f : (Σ a, P a) ≃ Σ b, Q b)
    (finiteF : ∀ a, (Set.range fun x : P a => (f ⟨a,x⟩).1).Finite)
    (finiteG : ∀ b, (Set.range fun y : Q b => (f.symm ⟨b,y⟩).1).Finite)
    (unionX : ∀ (I : Finset B) (U : B → Set X), (∀ b ∈ I, dimX (U b) ≤ d') →
      dimX (⋃ b ∈ I, U b) ≤ d')
    (unionY : ∀ (I : Finset A) (U : A → Set Y), (∀ a ∈ I, dimY (U a) ≤ d) →
      dimY (⋃ a ∈ I, U a) ≤ d)
    (embedF : ∀ a b, dimX (mixedSlice P Q f a b) ≤ dimY (Q b))
    (embedG : ∀ b a, dimY (mixedSlice Q P f.symm b a) ≤ dimX (P a))
    (source : IsLUB (Set.range fun a => dimX (P a)) d)
    (target : IsLUB (Set.range fun b => dimY (Q b)) d') : d = d' := by
  apply le_antisymm
  · apply source.2
    rintro _ ⟨a,rfl⟩
    exact fiber_dimension_le P Q d' dimX dimY f finiteF unionX embedF
      (fun b => target.1 ⟨b,rfl⟩) a
  · apply target.2
    rintro _ ⟨b,rfl⟩
    exact fiber_dimension_le Q P d dimY dimX f.symm finiteG unionY embedG
      (fun a => source.1 ⟨a,rfl⟩) b

end Dimension
end GeneralizedEuler.Section4
