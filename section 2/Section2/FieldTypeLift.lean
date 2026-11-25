module

public import Section2.ConvexLanguage
public import Section2.FieldGeneratedEmbedding
public import Section2.ValuedFieldFormulas

/-! Transfer of a one-point field type over matching parameters. The
saturation hypothesis is explicit, as in the use of the monster model
in Lemma 2.20. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v a

variable {L : Language.{u, v}} {K F : Type*} [L.Structure K] [L.Structure F]

/-- The part of saturation needed for one-point types over a family of
parameters indexed by `Names`. -/
@[expose]
def RealizesFinitelySatisfiableFieldTypes (L : Language.{u, v}) (F : Type*)
    [L.Structure F] (Names : Type a) : Prop :=
  ∀ v : Names → F, ∀ Δ : Set (L.Formula (Names ⊕ Unit)),
    (∀ U : Finset (L.Formula (Names ⊕ Unit)), (U : Set (L.Formula (Names ⊕ Unit))) ⊆ Δ →
      ∃ b : F, ∀ ψ ∈ U, ψ.Realize (Sum.elim v (fun _ => b))) →
    ∃ b : F, ∀ ψ ∈ Δ, ψ.Realize (Sum.elim v (fun _ => b))

theorem exists_fieldPoint_of_same_parameter_type {Names : Type a} (p : Names → K) (q : Names → F)
    (hmatch : ∀ φ : L.Formula Names, φ.Realize p ↔ φ.Realize q)
    (hsat : RealizesFinitelySatisfiableFieldTypes L F Names) (a : K) :
    ∃ b : F, ∀ ψ : L.Formula (Names ⊕ Unit),
      ψ.Realize (Sum.elim p (fun _ => a)) ↔ ψ.Realize (Sum.elim q (fun _ => b)) := by
  let Δ : Set (L.Formula (Names ⊕ Unit)) := {ψ | ψ.Realize (Sum.elim p (fun _ => a))}
  have hfinite (U : Finset (L.Formula (Names ⊕ Unit))) (hU : (↑U : Set _) ⊆ Δ) :
      ∃ b : F, ∀ ψ ∈ U, ψ.Realize (Sum.elim q (fun _ => b)) := by
    let χ : L.Formula (Names ⊕ Unit) := Formula.iInf (fun ψ : U => ψ.val)
    have hχ : (χ.iExs Unit).Realize p := by
      rw [Formula.realize_iExs]
      refine ⟨fun _ => a, ?_⟩
      exact Formula.realize_iInf.mpr (fun ψ => hU ψ.property)
    obtain ⟨z, hz⟩ := Formula.realize_iExs.mp ((hmatch (χ.iExs Unit)).mp hχ)
    refine ⟨z (), fun ψ hψ => ?_⟩
    have hz' := Formula.realize_iInf.mp hz ⟨ψ, hψ⟩
    have heq : z = fun _ => z () := funext (fun i => by cases i; rfl)
    rw [heq] at hz'
    exact hz'
  obtain ⟨b, hb⟩ := hsat q Δ hfinite
  refine ⟨b, fun ψ => ⟨fun h => hb ψ h, ?_⟩⟩
  intro h
  by_contra hp
  exact (Formula.realize_not.mp (hb ψ.not (Formula.realize_not.mpr hp))) h

/-- Quantifier elimination for the field reduct supplies the agreement on
parameters needed to obtain a field-language embedding of the simple
extension in the saturated target. -/
theorem exists_simpleFieldLift_of_QE {T : L.Theory} (hQE : EliminatesQuantifiers T)
    {A : Type a} [L.Structure A] [K ⊨ T] [F ⊨ T] [Nonempty K] [Nonempty F]
    (p : A ↪[L] K) (q : A ↪[L] F)
    (hsat : RealizesFinitelySatisfiableFieldTypes L F A) (a : K) :
    ∃ (b : F)
      (e : Substructure.closure L (Set.range (Sum.elim p (fun _ : Unit => a))) ↪[L] F),
      e ⟨a, Substructure.subset_closure ⟨.inr (), rfl⟩⟩ = b ∧
      ∀ c : A, e ⟨p c, Substructure.subset_closure ⟨.inl c, rfl⟩⟩ = q c := by
  have hmatch (φ : L.Formula A) : φ.Realize p ↔ φ.Realize q := by
    simpa only [Function.comp_id] using partialElementaryOfQE_anyVar hQE p q φ id
  obtain ⟨b, hb⟩ := exists_fieldPoint_of_same_parameter_type p q hmatch hsat a
  obtain ⟨e, he⟩ := exists_fieldGeneratedEmbedding _ _ hb
  exact ⟨b, e, he (.inr ()), fun c => he (.inl c)⟩

section NamedLeadingTerms

variable [Field K] [Field F]

set_option linter.style.haveILetI false in
/-- The second stage of Lemma 2.20 preserves every leading term named
by the common field representatives used to extend the field map. -/
theorem exists_simpleFieldLift_preserving_namedRV
    (O : ValuationSubring K) (P : ValuationSubring F)
    (terms : FieldTerms (convexLanguage L))
    (hK : letI := convexStructure O L; InterpretsFieldTerms (K := K) terms)
    (hF : letI := convexStructure P L; InterpretsFieldTerms (K := F) terms)
    {T : (convexLanguage L).Theory} (hQE : EliminatesQuantifiers T)
    {A : Type a} [(convexLanguage L).Structure A] {Names : Type*} :
    letI := convexStructure O L
    letI := convexStructure P L
    ∀ (p : A ↪[convexLanguage L] K) (q : A ↪[convexLanguage L] F)
      (_ : K ⊨ T) (_ : F ⊨ T)
      (_ : RealizesFinitelySatisfiableFieldTypes (convexLanguage L) F A)
      (a : K) (representative : Names → A),
      let B := Substructure.closure (convexLanguage L)
        (Set.range (Sum.elim p (fun _ : Unit => a)))
      ∃ (b : F) (e : B ↪[convexLanguage L] F),
        e ⟨a, Substructure.subset_closure ⟨.inr (), rfl⟩⟩ = b ∧
        (∀ c : A, e ⟨p c, Substructure.subset_closure ⟨.inl c, rfl⟩⟩ = q c) ∧
        ∀ (x : B) (t : Names),
          rv O x.val = rv O (p (representative t)) ↔
            rv P (e x) = rv P (q (representative t)) := by
  letI := convexStructure O L
  letI := convexStructure P L
  intro p q hTK hTF hsat a representative
  letI := hTK
  letI := hTF
  let B := Substructure.closure (convexLanguage L) (Set.range (Sum.elim p (fun _ : Unit => a)))
  obtain ⟨b, e, ha, he⟩ := exists_simpleFieldLift_of_QE hQE p q hsat a
  refine ⟨b, e, ha, he, ?_⟩
  intro x t
  let c : B := ⟨p (representative t), Substructure.subset_closure ⟨.inl (representative t), rfl⟩⟩
  let args : Fin 2 → B := fun i => if i = 0 then x else c
  have h := rv_eq_iff_of_pair_embeddings O P terms hK hF B.subtype e args
  have h0 : args 0 = x := by simp [args]
  have h1 : args 1 = c := by simp [args]
  rw [h0, h1, he (representative t)] at h
  exact h

end NamedLeadingTerms

end GeneralizedEuler.Section2
