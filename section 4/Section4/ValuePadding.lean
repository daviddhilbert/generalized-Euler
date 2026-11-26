module

public import Section4.ValueScissors
import all Section4.ValueScissors

/-! The class of an affine value graph in its original degree is the
class of its free domain times the point class to the number of omitted
coordinates. All equalities are in the positive value semiring. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder
open ValueObject
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {J : Language} [J.Structure V] (G : Submodule F V)

def zeroTuple (n : ℕ) : Set (Fin n → V) := {0}

theorem zeroTuple_definable (n : ℕ) : (G : Set V).Definable J (zeroTuple n) := by
  have d := Set.definable_iInter_of_finite (fun i : Fin n =>
    (Set.DefinableFun.proj (A := (G : Set V)) J (i := i)).ofPred_eq_const G.zero_mem)
  convert d using 1
  ext x; simp [zeroTuple,funext_iff]

def eValue : ValueObject.SemiringOfSets (J := J) (G : Set V) :=
  pieceClass (zeroTuple 1) (zeroTuple_definable G _)

theorem zeroTuple_product (n m : ℕ) : cartesian (zeroTuple (V := V) n) (zeroTuple m) = zeroTuple (n+m) := by
  ext x
  change (x ∘ finSumFinEquiv ∘ Sum.inl = 0 ∧ x ∘ finSumFinEquiv ∘ Sum.inr = 0) ↔ x = 0
  constructor
  · rintro ⟨h,k⟩
    funext i; obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    cases j with | inl j => exact congrFun h j | inr j => exact congrFun k j
  · rintro rfl; exact ⟨rfl,rfl⟩

private theorem class_congr {n} {D E : Set (Fin n → V)} (eq : D = E)
    (hd : (G : Set V).Definable J D) (he : (G : Set V).Definable J E) :
    pieceClass D hd = pieceClass E he := by subst E; rfl

theorem point_power (n : ℕ) : pieceClass (zeroTuple n) (zeroTuple_definable (J := J) G n) = eValue G ^ n := by
  induction n with
  | zero => exact (pieceClass_degree_zero _ _).trans (pow_zero _).symm
  | succ n ih =>
    have h := pieceClass_product (zeroTuple_definable (J := J) G n) (zeroTuple_definable (J := J) G 1)
    rw [pow_succ,← ih]
    exact (class_congr G (zeroTuple_product n 1).symm _ _).trans h

def padValues {r} (l : ℕ) (x : Fin r → V) : Fin (r+l) → V :=
  Sum.elim x 0 ∘ finSumFinEquiv.symm

theorem pad_injective {r l} : Function.Injective (padValues (V := V) (r := r) l) := by
  intro x y h; funext i
  simpa [padValues] using congrFun h (finSumFinEquiv (.inl i))

theorem pad_definable {r l} : (G : Set V).DefinableMap J (padValues (r := r) l) := by
  intro i
  obtain ⟨u,rfl⟩ := finSumFinEquiv.surjective i
  cases u with
  | inl j => simpa [padValues] using Set.DefinableFun.proj (A := (G : Set V)) J (i := j)
  | inr j => simpa [padValues] using J.definableFun_const (Fin r) G.zero_mem

theorem pad_image {r l} (D : Set (Fin r → V)) :
    padValues l '' D = cartesian D (zeroTuple l) := by
  ext x; constructor
  · rintro ⟨z,hz,rfl⟩
    change _ ∈ D ∧ _ = 0
    constructor
    · simpa [padValues,Function.comp_def] using hz
    · funext i; simp [padValues]
  · rintro ⟨hx,hz⟩
    refine ⟨_,hx,funext fun i => ?_⟩
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j => simp [padValues]
    | inr j => simpa [padValues] using (congrFun hz j).symm

theorem value_frame_class {r l} (h : ValueLanguage (J := J) G) (a : ValueFrame G r (r+l))
    (D : Set (Fin r → V)) (hd : (G : Set V).Definable J D) :
    pieceClass (a.eval '' D) (image_of_map _ (h.frame a) _ hd) = pieceClass D hd * eValue G ^ l := by
  have eq := pieceClass_images a.eval (padValues l) (h.frame a) (pad_definable G) D hd
    a.injective.injOn pad_injective.injOn
  have ec := eq.trans (class_congr G (pad_image D) _ (cartesian_definable hd (zeroTuple_definable G l)))
  exact ec.trans ((pieceClass_product hd (zeroTuple_definable G l)).trans
    (congrArg (pieceClass D hd * ·) (point_power G l)))

end GeneralizedEuler.Section4
