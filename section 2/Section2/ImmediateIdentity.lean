module

public import Section2.DirectedSubstructure

/-! Naming all leading terms in the domain of an immediate embedding. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {M : SortedStructure L E X}

/-- Keep the old VF sort and include every element of the ambient RV sort. -/
@[expose]
def SortedSubstructure.withAllRV (S : SortedSubstructure M) : SortedSubstructure M where
  carrier
    | .vf => S.carrier .vf
    | .rv => Set.univ
  closed := by
    intro ss s f x hx
    cases f with
    | vf f =>
      let carrier : ∀ s, Set (X s)
        | .vf => S.carrier .vf
        | .rv => Set.univ
      have old {s : TCsort} (hs : s = .vf) (x : X s) :
          x ∈ carrier s → x ∈ S.carrier s := by
        subst s
        exact id
      exact S.closed (.vf f) x (fun i => old (by simp [List.get_eq_getElem]) (x i) (hx i))
    | rvZero | rvOne | rvMul | rvInv | residue | power | rv => exact Set.mem_univ _

private def identityOnRV (S : SortedSubstructure M) (e : SortedEmbedding S.structureOn M) :
    ∀ s, S.withAllRV.carrier s ↪ X s
  | .vf => e.toEmbedding .vf
  | .rv => Function.Embedding.subtype _

private theorem withAllRV_vfArgs (S : SortedSubstructure M)
    (e : SortedEmbedding S.structureOn M) {ss : List TCsort}
    (h : ∀ i : Fin ss.length, ss.get i = .vf)
    (a : SortedArgs (fun s => S.withAllRV.carrier s) ss) :
    ∃ b : SortedArgs (fun s => S.carrier s) ss,
      (fun i => (b i).val) = (fun i => (a i).val) ∧
      (fun i => e.toEmbedding _ (b i)) = (fun i => identityOnRV S e _ (a i)) := by
  have oldArg {s : TCsort} (hs : s = .vf) (x : S.withAllRV.carrier s) :
      ∃ y : S.carrier s, y.val = x.val ∧ e.toEmbedding s y = identityOnRV S e s x := by
    subst s
    exact ⟨x, rfl, rfl⟩
  choose b hb he using fun i => oldArg (h i) (a i)
  exact ⟨b, funext hb, funext he⟩

private theorem withAllRV_rvArgs (S : SortedSubstructure M)
    (e : SortedEmbedding S.structureOn M) {n : ℕ}
    (a : SortedArgs (fun s => S.withAllRV.carrier s) (List.replicate n .rv)) :
    (fun i => (a i).val) = (fun i => identityOnRV S e _ (a i)) := by
  have eq {s : TCsort} (hs : s = .rv) (x : S.withAllRV.carrier s) :
      x.val = identityOnRV S e s x := by
    subst s
    rfl
  exact funext fun i => eq (by simp [List.get_eq_getElem]) (a i)

/-- An immediate embedding extends by the identity on all of RV,
without adjoining any field elements. -/
def SortedEmbedding.extendImmediateByIdentity (S : SortedSubstructure M)
    (e : SortedEmbedding S.structureOn M)
    (hfix : ∀ t : S.carrier .rv, e.toEmbedding .rv t = t.val) :
    FixedRVLift M M Set.univ where
  source := S.withAllRV
  rv_eq := rfl
  embedding :=
    { toEmbedding := identityOnRV S e
      map_fun := by
        intro ss s f a
        cases f with
        | vf f =>
          obtain ⟨b, hb, he⟩ := withAllRV_vfArgs S e (fun i => by
            simp [List.get_eq_getElem]) a
          have hf : S.structureOn.funMap (.vf f) b = S.withAllRV.structureOn.funMap (.vf f) a :=
            Subtype.ext (congrArg (M.funMap (.vf f)) hb)
          change e.toEmbedding .vf (S.withAllRV.structureOn.funMap (.vf f) a) = _
          rw [← hf, ← he]
          exact e.map_fun (.vf f) b
        | rv =>
          obtain ⟨b, hb, he⟩ := withAllRV_vfArgs S e (fun i => by
            have hi : i = (0 : Fin 1) := Fin.fin_one_eq_zero i
            subst i
            rfl) a
          change M.funMap .rv (fun i => (a i).val) = _
          rw [← hb, ← he]
          exact (hfix (S.structureOn.funMap .rv b)).symm.trans (e.map_fun .rv b)
        | rvZero | rvOne =>
          exact congrArg (M.funMap _) (withAllRV_rvArgs S e (n := 0) a)
        | rvMul =>
          exact congrArg (M.funMap _) (withAllRV_rvArgs S e (n := 2) a)
        | rvInv | power =>
          exact congrArg (M.funMap _) (withAllRV_rvArgs S e (n := 1) a)
        | residue =>
          exact congrArg (M.funMap _) (withAllRV_rvArgs S e a)
      map_rel := by
        intro ss r a
        cases r with
        | vf r =>
          obtain ⟨b, hb, he⟩ := withAllRV_vfArgs S e (fun i => by
            simp [List.get_eq_getElem]) a
          change M.relMap (.vf r) _ ↔ M.relMap (.vf r) _
          rw [← he, ← hb]
          exact e.map_rel (.vf r) b
        | residueNonzero =>
          exact (congrArg (M.relMap _) (withAllRV_rvArgs S e (n := 1) a).symm).to_iff
        | rvLE =>
          exact (congrArg (M.relMap _) (withAllRV_rvArgs S e (n := 2) a).symm).to_iff }

theorem SortedEmbedding.extendImmediateByIdentity_fixesRV (S : SortedSubstructure M)
    (e : SortedEmbedding S.structureOn M)
    (hfix : ∀ t : S.carrier .rv, e.toEmbedding .rv t = t.val)
    (t : (e.extendImmediateByIdentity S hfix).source.carrier .rv) :
    (e.extendImmediateByIdentity S hfix).embedding.toEmbedding .rv t = t.val := by
  rfl

@[simp]
theorem SortedEmbedding.extendImmediateByIdentity_carrier_vf (S : SortedSubstructure M)
    (e : SortedEmbedding S.structureOn M)
    (hfix : ∀ t : S.carrier .rv, e.toEmbedding .rv t = t.val) :
    (e.extendImmediateByIdentity S hfix).source.carrier .vf = S.carrier .vf := by
  rfl

theorem SortedEmbedding.extendImmediateByIdentity_agrees (S : SortedSubstructure M)
    (e : SortedEmbedding S.structureOn M)
    (hfix : ∀ t : S.carrier .rv, e.toEmbedding .rv t = t.val)
    (s : TCsort) (x : S.carrier s)
    (hx : x.val ∈ (e.extendImmediateByIdentity S hfix).source.carrier s) :
    (e.extendImmediateByIdentity S hfix).embedding.toEmbedding s ⟨x.val, hx⟩ =
      e.toEmbedding s x := by
  cases s with
  | vf => rfl
  | rv => exact (hfix x).symm

end GeneralizedEuler.Section2
