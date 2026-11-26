module

public import Section5.VerticalPositioning
public import Section5.UnaryWitnessPreparation

/-! After contracting one field coordinate, retaining its new leading
term preserves finite label fibers over the other field coordinates. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K) {T H R : Type*}

@[expose] def verticalContractionLabels
    (A : Set (K × T × R)) (P : T → UnaryPreparation O H) (b : T) : Set (H × R) :=
  {p | ∃ x, (x,b,p.2) ∈ A ∧ (P b).label x = p.1}

theorem vertical_contracted_labels_finite_over_selected {Q₀ : Type*}
    (A : Set (K × T × R)) (P : T → UnaryPreparation O H)
    (selected : R → Q₀)
    (finite : ∀ x b q, {a : R | (x,b,a) ∈ A ∧ selected a = q}.Finite)
    (offsets : ∀ b, (Set.range (P b).offset).Finite)
    (constant : ∀ b x y a, (P b).label x = (P b).label y → ((x,b,a) ∈ A ↔ (y,b,a) ∈ A)) :
    ∀ b (t : RV0 O) q, {p ∈ verticalContractionLabels O A P b | (P b).lead p.1 = t ∧ selected p.2 = q}.Finite := by
  intro b t q
  let Q := P b
  obtain ⟨y,ry⟩ := rv_surjective O t
  let preimage := (y + ·) '' Set.range Q.offset
  let labeled (x : K) := (fun a : R => (Q.label x,a)) '' {a | (x,b,a) ∈ A ∧ selected a = q}
  have fin : (⋃ x ∈ preimage, labeled x).Finite :=
    ((offsets b).image _).biUnion (fun x _ => (finite x b q).image _)
  apply fin.subset
  rintro ⟨h,a⟩ ⟨⟨x,mem,hx⟩,lead,select⟩
  let z := y + Q.offset h
  have lab : Q.label z = h := by
    refine ((Q.label_eq_iff (x := x) (y := z)).2 ?_).trans hx
    change rv O (y + Q.offset h - Q.offset (Q.label x)) = Q.lead (Q.label x)
    rw [hx,add_sub_cancel_right,ry,lead]
  have mz : (z,b,a) ∈ A := (constant b z x a (lab.trans hx.symm)).2 mem
  exact Set.mem_iUnion₂.2 ⟨z,⟨Q.offset h,⟨h,rfl⟩,rfl⟩,a,⟨mz,select⟩,Prod.ext lab rfl⟩

theorem vertical_contracted_labels_finite_over_lead
    (A : Set (K × T × R)) (P : T → UnaryPreparation O H)
    (finite : ∀ x b, {a : R | (x,b,a) ∈ A}.Finite)
    (offsets : ∀ b, (Set.range (P b).offset).Finite)
    (constant : ∀ b x y a, (P b).label x = (P b).label y → ((x,b,a) ∈ A ↔ (y,b,a) ∈ A)) :
    ∀ b (t : RV0 O), {p ∈ verticalContractionLabels O A P b | (P b).lead p.1 = t}.Finite := by
  intro b t
  have fin (x : K) (b : T) (q : Unit) : {a : R | (x,b,a) ∈ A ∧ () = q}.Finite :=
    (finite x b).subset (fun _ h => h.1)
  have res := vertical_contracted_labels_finite_over_selected O A P (fun _ => ()) fin offsets constant b t ()
  simpa only [and_true] using res

end GeneralizedEuler.Section5
