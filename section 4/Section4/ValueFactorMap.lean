module

public import Section4.ValueDescent
public import Section4.ValuePullback
import all Section4.ValuePullback
import all Section4.ValueScissors
import all Section4.Scissors
import all Section4.FiniteScissors

/-! The value-factor map on the graded Grothendieck semiring, obtained
from definable pullbacks and the single-piece lifting theorem. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder GeneralizedEuler.Section2 ValueObject
variable {L J : Language} {E : Type*} {Z : TCsort → Type*} {Γ : Type*} [J.Structure Γ]
  (M : SortedStructure L E Z) (S : SortedSubstructure M) (v : Z .rv → Γ) (A : Set Γ)

theorem rv_reindex_equivalent {I H : Type} [Finite H] (p : H ≃ I)
    (D : Set (I → Z .rv)) (hd : isRVSet M S D) :
    RVDefinablyEquivalent M S.carrier D {y | y ∘ p.symm ∈ D} := by
  let e : D ≃ {y | y ∘ p.symm ∈ D} :=
    { toFun := fun x => ⟨x.val ∘ p,by simp [Function.comp_def]⟩
      invFun := fun y => ⟨y.val ∘ p.symm,y.property⟩
      left_inv := fun x => Subtype.ext (funext fun i => congrArg x.val (p.apply_symm_apply i))
      right_inv := fun y => Subtype.ext (funext fun j => congrArg y.val (p.symm_apply_apply j)) }
  let Var := RVVariables (I ⊕ H)
  have d : isRVSet M S {w : I ⊕ H → Z .rv | w ∘ Sum.inl ∈ D} := isRVSet_precomp Sum.inl hd
  have g := d.inter (SortedDefinableOver.iInter (fun j : H =>
    SortedDefinableOver.coordinate_eq (M := M) (A := S.carrier) (Var := Var) .rv (.inl (p j)) (.inr j)))
  refine ⟨e,?_⟩
  convert g using 1
  ext w
  change (∃ x : D, x.val = w .rv ∘ Sum.inl ∧ x.val ∘ p = w .rv ∘ Sum.inr) ↔
    _ ∧ w ∈ ⋂ j : H, {a | a .rv (.inl (p j)) = a .rv (.inr j)}
  simp only [Set.mem_iInter,Set.mem_ofPred_eq]
  exact ⟨fun ⟨x,hx,hy⟩ => ⟨hx ▸ x.property,fun j => (congrFun hx (p j)).symm.trans (congrFun hy j)⟩,
    fun ⟨hw,hy⟩ => ⟨⟨_,hw⟩,rfl,funext hy⟩⟩

variable
  (defSharp : ∀ {k} {D : Set (Fin k → Γ)}, A.Definable J D → isRVSet M S (sharp M v D))
  (liftIso : ∀ {k} (D B : Set (Fin k → Γ)), A.Definable J D → A.Definable J B →
    ∀ e : D ≃ B, A.Definable J {w : Fin k ⊕ Fin k → Γ |
        ∃ x : D, x.val = w ∘ Sum.inl ∧ (e x).val = w ∘ Sum.inr} →
      RVDefinablyEquivalent M S.carrier (sharp M v D) (sharp M v B))

def sharpMeasure : PieceMeasure J A (RVSemiring M S) where
  weight D hd := objectClass M S ⟨_,sharpObject M S v D (defSharp hd)⟩
  empty k := by
    apply scissors_sound M S; apply RVRelation.zero
    exact Set.eq_empty_iff_forall_notMem.mpr fun _ hx => hx.2
  one := by
    apply scissors_sound M S; apply RVRelation.one
    refine ⟨fun i : Fin 0 => i.elim0,Set.ext fun x => ?_⟩
    change (_ ∧ _) ↔ x = (fun i : Fin 0 => i.elim0)
    exact ⟨fun _ => funext (fun i : Fin 0 => i.elim0),fun _ => ⟨fun j => j.elim0,Set.mem_univ _⟩⟩
  cut D B hd hb h := sharp_cut M S v (defSharp (hd.union hb)) (defSharp hd) (defSharp hb) rfl h
  iso D B hd hb e hg := scissors_sound M S (RVRelation.iso _ _ (liftIso D B hd hb e hg))
  prod {k l} D B hd hb := by
    apply scissors_sound M S
    apply RVRelation.prod
    let P := productSet (sharp M v D) (sharp M v B)
    have hp : isRVSet M S P := (isRVSet_precomp Sum.inl (defSharp hd)).inter
      (isRVSet_precomp Sum.inr (defSharp hb))
    have eq : {y : Fin (k+l) → Z .rv | y ∘ finSumFinEquiv ∈ P} = sharp M v (cartesian D B) := by
      ext y
      change ((_ ∧ _) ∧ _ ∧ _) ↔ (∀ j, _) ∧ _ ∧ _
      constructor
      · rintro ⟨⟨h,d⟩,h',b⟩
        refine ⟨fun j => ?_,d,b⟩
        obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective j
        cases i with | inl a => exact h a | inr a => exact h' a
      · rintro ⟨h,d,b⟩
        exact ⟨⟨fun i => h _,d⟩,fun j => h _,b⟩
    change RVDefinablyEquivalent M S.carrier P (sharp M v (cartesian D B))
    rw [← eq]
    exact rv_reindex_equivalent M S finSumFinEquiv.symm P hp

def valueFactorHom : SemiringOfSets (J := J) A →+* RVSemiring M S :=
  (sharpMeasure M S v A defSharp liftIso).descend

theorem valueFactorHom_piece {k} (D : Set (Fin k → Γ)) (hd : A.Definable J D) :
    valueFactorHom M S v A defSharp liftIso (pieceClass D hd) =
      objectClass M S ⟨k,sharpObject M S v D (defSharp hd)⟩ :=
  (sharpMeasure M S v A defSharp liftIso).descend_piece D hd

end GeneralizedEuler.Section4
