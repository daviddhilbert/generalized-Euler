module

public import Section5.FiniteProjectionElementaryLift
public import Section5.PositiveBlowupObject

/-! Identify the two multiplier cases with the lifts of the actual
graded blowup objects. The smaller field arity is padded by zero. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {L : Language} [L.Structure K] {E : Type*}
  (O : ValuationSubring K) [L.Structure (Residue O)]
  (hO : IsOrderConvex O) (power : E → RV0 O → RV0 O)
  (S : SortedSubstructure (canonicalStructure (L := L) O hO power))
  {k m : ℕ}
  (U : RVObject (canonicalStructure (L := L) O hO power) S (k+1))
  (j : Fin (k+1))
  (finiteDelete : ∀ t : Fin k → RV0 O, {u ∈ Set.range U.label | u ∘ j.succAbove = t}.Finite)

local notation "𝓜" => canonicalStructure (L := L) O hO power

theorem elementary_zero_iff_padded_lift
    (w : SortedAssignment (CanonicalSort O) (ElementaryLiftVars O hO power S U)) :
    let v : SortedAssignment (CanonicalSort O) (ObjectLift.Vars (zeroBlowupObject U j finiteDelete)) :=
      fun s => match s with
      | .vf => w .vf ∘ j.succAbove
      | .rv => w .rv ∘ Sum.inl
    (w ∈ elementaryLiftCarrier O hO power S U j ∧ w .rv (.inr ()) = 0) ↔
      v ∈ ObjectLift.carrier (zeroBlowupObject U j finiteDelete) ∧
        w .vf j = 0 ∧ w .rv (.inr ()) = 0 := by
  intro v
  constructor
  · rintro ⟨⟨a,ha,_,hw⟩,hm⟩
    refine ⟨⟨a,ha,?_⟩,?_,hm⟩
    · funext i
      change U.label a (j.succAbove i) = (canonicalStructure (L := L) O hO power).rvMap (w .vf (j.succAbove i))
      rw [canonicalStructure_rvMap]
      have h := hw (j.succAbove i)
      rw [blowupLabel,Function.update_of_ne (Fin.succAbove_ne j i)] at h
      exact h.symm
    · apply (rv_eq_zero_iff O).1
      have h := hw j
      rw [blowupLabel,Function.update_self,hm] at h
      change rv O (w .vf j) = (0 : RV0 O) * U.label a j at h
      exact h.trans (zero_mul (U.label a j))
  · rintro ⟨⟨a,ha,hg⟩,hf,hm⟩
    refine ⟨⟨a,ha,by rw [hm,map_zero]; exact zero_lt_one,?_⟩,hm⟩
    intro i
    by_cases he : i = j
    · subst i
      rw [blowupLabel,Function.update_self,hf,hm]
      change rv O 0 = (0 : RV0 O) * U.label a j
      exact (map_zero (rv O)).trans (zero_mul (U.label a j)).symm
    · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq he
      rw [blowupLabel,Function.update_of_ne (Fin.succAbove_ne j l)]
      have h := congrFun hg l
      change U.label a (j.succAbove l) =
        (canonicalStructure (L := L) O hO power).rvMap (w .vf (j.succAbove l)) at h
      rw [canonicalStructure_rvMap] at h
      exact h.symm

theorem elementary_nonzero_iff_lift
    (idx : Fin m ≃ Fin U.arity ⊕ Fin 1) (hneg : rv O (-1) ∈ S.carrier .rv)
    (w : SortedAssignment (CanonicalSort O) (ElementaryLiftVars O hO power S U)) :
    let V := positiveBlowupObject O hO power S U idx hneg j finiteDelete
    let v : SortedAssignment (CanonicalSort O) (ObjectLift.Vars V) :=
      fun s => match s with
      | .vf => w .vf
      | .rv => w .rv ∘ Sum.map id (fun _ => ()) ∘ idx
    (w ∈ elementaryLiftCarrier O hO power S U j ∧ w .rv (.inr ()) ≠ 0) ↔ v ∈ ObjectLift.carrier V := by
  intro V v
  let t := w .rv ∘ Sum.map id (fun _ : Fin 1 => ()) ∘ idx
  have old : t ∘ idx.symm ∘ Sum.inl = w .rv ∘ Sum.inl := by
    funext i
    simp only [t,Function.comp_apply,Equiv.apply_symm_apply,Sum.map_inl,id_eq]
  have mult : t (idx.symm (.inr 0)) = w .rv (.inr ()) := by
    simp only [t,Function.comp_apply,Equiv.apply_symm_apply,Sum.map_inr]
  constructor
  · rintro ⟨⟨a,ha,hm,hx⟩,hn⟩
    have prop : t ∈ V.carrier := by
      change (t ∘ idx.symm ∘ Sum.inl) ∈ U.carrier ∧
        unsignedValue O (t (idx.symm (.inr 0))) < 1 ∧ t (idx.symm (.inr 0)) ≠ 0
      rw [old,mult]
      exact ⟨ha ▸ a.property,hm,hn⟩
    refine ⟨⟨t,prop⟩,rfl,?_⟩
    funext i
    have hTag : (⟨t ∘ idx.symm ∘ Sum.inl,prop.1⟩ : U.carrier) = a := Subtype.ext (old.trans ha.symm)
    change blowupLabel O j U.label (⟨t ∘ idx.symm ∘ Sum.inl,prop.1⟩,t (idx.symm (.inr 0))) i =
      (canonicalStructure (L := L) O hO power).rvMap (w .vf i)
    rw [hTag,mult,canonicalStructure_rvMap]
    exact (hx i).symm
  · rintro ⟨a,ha,hx⟩
    have h : a.val = t := ha
    have oldA : a.val ∘ idx.symm ∘ Sum.inl = w .rv ∘ Sum.inl :=
      (congrArg (fun u => u ∘ idx.symm ∘ Sum.inl) h).trans old
    have multA : a.val (idx.symm (.inr 0)) = w .rv (.inr ()) :=
      (congrFun h _).trans mult
    have prop := a.property
    change (a.val ∘ idx.symm ∘ Sum.inl) ∈ U.carrier ∧
      unsignedValue O (a.val (idx.symm (.inr 0))) < 1 ∧ a.val (idx.symm (.inr 0)) ≠ 0 at prop
    let u : U.carrier := ⟨a.val ∘ idx.symm ∘ Sum.inl,prop.1⟩
    refine ⟨⟨u,oldA,multA ▸ prop.2.1,?_⟩,multA ▸ prop.2.2⟩
    intro i
    have he := congrFun hx i
    change blowupLabel O j U.label (u,a.val (idx.symm (.inr 0))) i =
      (canonicalStructure (L := L) O hO power).rvMap (w .vf i) at he
    rw [multA,canonicalStructure_rvMap] at he
    exact he.symm

end GeneralizedEuler.Section5
