module

public import Section5.LiftBoundaryDimension
public import Section4.TaggedObjects
import all Section2.RVDefinableEquivalence

/-! The field lift of an RV object retains its RV point as well as the
field representatives of the structure coordinates. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M} {k : ℕ}

namespace ObjectLift

abbrev Vars (U : RVObject M S k) := MixedVariables k (Fin U.arity)

@[expose] def carrier (U : RVObject M S k) : Set (SortedAssignment X (Vars U)) :=
  {x | ∃ u : U.carrier, u.val = x .rv ∧ U.label u = M.rvMap ∘ x .vf}

theorem definable (U : RVObject M S k) :
    SortedDefinableOver M S.carrier (carrier U) := by
  let V := Vars U
  let W := RVVariables (Fin k)
  let T := SumVariables V W
  let tagRename : ∀ s, RVVariables (Fin U.arity ⊕ Fin k) s → T s
    | .vf => PEmpty.elim
    | .rv => id
  let leadRename : ∀ s, SumVariables (MixedVariables k Empty) W s → T s
    | .vf => Sum.map id id
    | .rv => Sum.map Empty.elim id
  have hTag := U.graph.pullback_relabel tagRename
  have hLead := fieldLead_definable (M := M) (S := S) (n := k)
  unfold DefinableRelation at hLead
  have hh := definable_project_mixed (hTag.inter (hLead.pullback_relabel leadRename))
  convert hh using 1
  ext a
  let left (b : labelAssignment k X) : fieldAssignment k X :=
    fun s => (Sum.elim (a s) (b s) ∘ leadRename s) ∘ Sum.inl
  let right (b : labelAssignment k X) : labelAssignment k X :=
    fun s => (Sum.elim (a s) (b s) ∘ leadRename s) ∘ Sum.inr
  have eLeft (b : labelAssignment k X) : left b = fieldTupleAssignment (a .vf) := by
    funext s i
    cases s with
    | vf => rfl
    | rv => exact i.elim
  have eRight (b : labelAssignment k X) : right b = b := by
    funext s i
    cases s with
    | vf => exact i.elim
    | rv => rfl
  change (∃ u : U.carrier, u.val = a .rv ∧ U.label u = M.rvMap ∘ a .vf) ↔
    ∃ b : labelAssignment k X, (∃ u : U.carrier, u.val = a .rv ∧ U.label u = b .rv) ∧
      fieldLead M (left b) = right b
  simp only [eLeft,eRight]
  constructor
  · rintro ⟨u,hu,hLab⟩
    exact ⟨fieldLead M (fieldTupleAssignment (a .vf)),⟨u,hu,hLab⟩,rfl⟩
  · rintro ⟨_,⟨u,hu,hLab⟩,rfl⟩
    exact ⟨u,hu,hLab⟩

/-- The RV point of the lifted tuple. -/
def tag (U : RVObject M S k) (x : carrier U) : U.carrier := x.property.choose

theorem tag_val (U : RVObject M S k) (x : carrier U) : (tag U x).val = x.val .rv :=
  x.property.choose_spec.1

theorem tag_label (U : RVObject M S k) (x : carrier U) :
    U.label (tag U x) = M.rvMap ∘ x.val .vf :=
  x.property.choose_spec.2

theorem tag_of_val_eq (U : RVObject M S k) (x : carrier U) (a : U.carrier)
    (h : a.val = x.val .rv) : tag U x = a :=
  Subtype.ext ((tag_val U x).trans h.symm)

@[expose] def assemble (U : RVObject M S k) (a : U.carrier) (x : Fin k → X .vf)
    (h : U.label a = M.rvMap ∘ x) : carrier U :=
  ⟨fun s => match s with
    | .vf => x
    | .rv => a.val, ⟨a,rfl,h⟩⟩

theorem assemble_tag (U : RVObject M S k) (a : U.carrier) (x : Fin k → X .vf)
    (h : U.label a = M.rvMap ∘ x) : tag U (assemble U a x h) = a :=
  tag_of_val_eq U _ a rfl

theorem ext {U : RVObject M S k} {x y : carrier U}
    (field : x.val .vf = y.val .vf) (rv : tag U x = tag U y) : x = y := by
  apply Subtype.ext
  funext s i
  cases s with
  | vf => exact congrFun field i
  | rv =>
    have h := ((tag_val U x).symm.trans (congrArg Subtype.val rv)).trans (tag_val U y)
    exact congrFun h i

/-- For a fixed field tuple the tags inject into one fiber of the RV
structure map. Thus a lift is an object of the finite-fiber VF category. -/
theorem finite_field_fiber (U : RVObject M S k) (a : Fin k → X .vf) :
    {x : carrier U | x.val .vf = a}.Finite := by
  have inj : Set.InjOn (tag U) {x : carrier U | x.val .vf = a} := by
    intro x hx y hy he
    exact ext (hx.trans hy.symm) he
  apply (U.finiteFibers (M.rvMap ∘ a)).of_injOn (f := tag U) ?_ inj
  intro x hx
  change U.label (tag U x) = M.rvMap ∘ a
  rw [tag_label U x]
  exact congrArg (M.rvMap ∘ ·) hx

end ObjectLift

end GeneralizedEuler.Section5
