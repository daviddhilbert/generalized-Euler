module

public import Section4.Factors

public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2 FirstOrder
variable {L : Language} {E : Type*} {Z : TCsort → Type*}
  (M : SortedStructure L E Z) (S : SortedSubstructure M)

theorem definable_identity_label {k} {D : Set (Fin k → Z .rv)} (hD : isRVSet M S D) :
    SortedDefinableOver M S.carrier (rvGraph (fun x : D => x.val)) := by
  let V := RVVariables (Fin k ⊕ Fin k)
  let rename : ∀ s, RVVariables (Fin k) s → V s
    | .vf => PEmpty.elim
    | .rv => Sum.inl
  let dom : Set (∀ s, V s → Z s) := {x | x .rv ∘ Sum.inl ∈ D}
  have hd : SortedDefinableOver M S.carrier dom := hD.pullback_relabel rename
  have he := SortedDefinableOver.iInter (fun j : Fin k =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := V) .rv (.inl j) (.inr j))
  convert hd.inter he using 1
  ext x
  change (∃ t : D, t.val = x .rv ∘ Sum.inl ∧ t.val = x .rv ∘ Sum.inr) ↔
    x .rv ∘ Sum.inl ∈ D ∧ x ∈ ⋂ j : Fin k, {y | y .rv (.inl j) = y .rv (.inr j)}
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t,hi,hj⟩
    exact ⟨hi ▸ t.property,congrFun (hi.symm.trans hj)⟩
  · rintro ⟨h,e⟩; exact ⟨⟨_,h⟩,rfl,funext e⟩

/-- The value domain uses nonzero representatives in every coordinate. This
condition is vacuous in degree zero. -/
def sharp {Γ : Type*} (v : Z .rv → Γ) {k} (D : Set (Fin k → Γ)) : Set (Fin k → Z .rv) :=
  {x | (∀ j, x j ≠ M.funMap .rvZero (fun i => i.elim0)) ∧ v ∘ x ∈ D}

def sharpObject {Γ : Type*} (v : Z .rv → Γ) {k} (D : Set (Fin k → Γ))
    (hd : isRVSet M S (sharp M v D)) : RVObject M S k where
  arity := k
  carrier := sharp M v D
  definable := hd
  label := Subtype.val
  graph := definable_identity_label M S hd
  nonzero := fun t => t.property.1
  finiteFibers := fun y => (Set.finite_singleton y).preimage Subtype.val_injective.injOn

/-- A disjoint cut of a value piece gives a cut of its pullback in the RV
semiring before groupification. -/
theorem sharp_cut {Γ : Type*} (v : Z .rv → Γ) {k} {D A B : Set (Fin k → Γ)}
    (hd : isRVSet M S (sharp M v D)) (ha : isRVSet M S (sharp M v A))
    (hb : isRVSet M S (sharp M v B)) (cover : A ∪ B = D) (disj : Disjoint A B) :
    objectClass M S ⟨k,sharpObject M S v D hd⟩ =
      objectClass M S ⟨k,sharpObject M S v A ha⟩ + objectClass M S ⟨k,sharpObject M S v B hb⟩ := by
  subst D
  apply scissors_sound M S
  apply RVRelation.cut _ _ _ (sharp M v A) (sharp M v B) ha hb
  · exact Set.disjoint_left.mpr fun _ h h' => Set.disjoint_left.mp disj h.2 h'.2
  · ext t
    exact and_or_left.symm
  · exact ⟨Equiv.refl _,definable_identity_label M S ha⟩
  · exact ⟨Equiv.refl _,definable_identity_label M S hb⟩

end GeneralizedEuler.Section4
