module

public import Section4.UnaryFiberMatching
import all Section4.TupleFibers
import all Section4.UnaryFiberMatching

/-! Match fibers in a disjoint union of rectangles. The tag includes the
residue tuple, which each shear fixes. The height may vary with the tag. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4

variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T]
  [AddCommGroup V] [Module F V] (v : T →ₗ[F] V) (G : Submodule F V)

structure FiberFamily (V : Type*) where
  Tag : Type*
  height : Tag → ℕ
  domain : (i : Tag) → Set (Fin (height i) → V)

namespace FiberFamily
variable (A : FiberFamily V)

abbrev Label := (i : A.Tag) × A.domain i

abbrev Lift := (i : A.Tag) × {x : Fin (A.height i) → T // v ∘ x ∈ A.domain i}

def label (x : A.Lift v) : A.Label := ⟨x.1, v ∘ x.2.val, x.2.property⟩

theorem label_surjective (surj : Function.Surjective v) : Function.Surjective (A.label v) := by
  rintro ⟨i,a⟩
  choose rep law using surj
  have eq : v ∘ (rep ∘ a.val) = a.val := funext fun j => law _
  exact ⟨⟨i,rep ∘ a.val,eq.symm ▸ a.property⟩,Sigma.ext rfl (heq_of_eq (Subtype.ext eq))⟩

def move (L : (V ⧸ G) →ₗ[F] v.ker) (x : A.Lift v) : A.Lift v :=
  ⟨x.1,shear v G L ∘ x.2.val,by
    have eq : v ∘ (shear v G L ∘ x.2.val) = v ∘ x.2.val := funext fun _ => shear_preserves_value _ _ _ _
    exact eq.symm ▸ x.2.property⟩

theorem label_move (L : (V ⧸ G) →ₗ[F] v.ker) (x : A.Lift v) :
    A.label v (A.move v G L x) = A.label v x :=
  Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun _ => shear_preserves_value _ _ _ _)))

theorem move_transitive {x z : A.Lift v} (eq : A.label v x = A.label v z)
    (ind : LinearIndependent F (G.mkQ ∘ v ∘ x.2.val)) : ∃ L, A.move v G L x = z := by
  obtain ⟨i,x⟩ := x
  obtain ⟨j,z⟩ := z
  obtain rfl : i=j := congrArg Sigma.fst eq
  have same : v ∘ x.val = v ∘ z.val := congrArg Subtype.val (Sigma.mk.inj_iff.mp eq).2.eq
  obtain ⟨L,hL⟩ := transitive_independent_fiber v G _ _ ind same
  exact ⟨L,Sigma.ext rfl (heq_of_eq (Subtype.ext hL))⟩

variable {A} {B : FiberFamily V} (f : A.Lift v ≃ B.Lift v)
  (comm : ∀ L x, f (A.move v G L x) = B.move v G L (f x))

include comm in
theorem span_preserved (d : v.ker) (hd : d ≠ 0) (x : A.Lift v) :
    valueSpan v G x.2.val = valueSpan v G (f x).2.val := by
  let i := x.1
  let j := (f x).1
  let graph (a : Fin (A.height i) → T) (b : Fin (B.height j) → T) :=
    ∃ (ha : v ∘ a ∈ A.domain i) (hb : v ∘ b ∈ B.domain j),
      f ⟨i,a,ha⟩ = ⟨j,b,hb⟩
  apply span_eq_of_shear_bijection v G graph _ _ _ d hd
  · exact ⟨x.2.property,(f x).2.property,rfl⟩
  · rintro L a b ⟨ha,hb,h⟩
    let u : A.Lift v := ⟨i,a,ha⟩
    let w : B.Lift v := ⟨j,b,hb⟩
    exact ⟨(A.move v G L u).2.property,(B.move v G L w).2.property,
      (comm L u).trans (congrArg (B.move v G L) h)⟩
  · rintro a a' b ⟨_,_,h⟩ ⟨_,_,h'⟩
    exact congrArg Subtype.val (Sigma.mk.inj_iff.mp (f.injective (h.trans h'.symm))).2.eq
  · rintro a b b' ⟨_,_,h⟩ ⟨_,_,h'⟩
    exact congrArg Subtype.val (Sigma.mk.inj_iff.mp (h.symm.trans h')).2.eq

include comm in
theorem maximal_whole_match (d : v.ker) (hd : d ≠ 0) (x : A.Lift v)
    (ind : LinearIndependent F (G.mkQ ∘ v ∘ x.2.val))
    (maximal : B.height (f x).1 ≤ A.height x.1) :
    B.height (f x).1 = A.height x.1 ∧
    WholeMatch (A.label v) (B.label v) f (A.label v x) (B.label v (f x)) := by
  obtain ⟨height,ind'⟩ := independent_at_max_height v G x.2.val (f x).2.val ind
    (span_preserved v G f comm d hd x) maximal
  refine ⟨height,Set.ext fun y => ?_⟩
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨L,rfl⟩ := A.move_transitive v G (Eq.symm hz) ind
    rw [comm]
    exact B.label_move v G L (f x)
  · intro hy
    obtain ⟨L,rfl⟩ := B.move_transitive v G (Eq.symm hy) ind'
    exact ⟨A.move v G L x,A.label_move v G L x,comm L x⟩

include comm in
theorem unmatched_dependent (surj : Function.Surjective v) (d : v.ker) (hd : d ≠ 0)
    (a : A.Label) (maximal : ∀ j, B.height j ≤ A.height a.1)
    (unmatched : ¬ ∃ b, WholeMatch (A.label v) (B.label v) f a b) :
    ¬ LinearIndependent F (G.mkQ ∘ a.2.val) := by
  obtain ⟨x,rfl⟩ := A.label_surjective v surj a
  exact fun ind => unmatched ⟨_,(maximal_whole_match v G f comm d hd x ind (maximal _)).2⟩

include comm in
theorem inverse_commutes (L : (V ⧸ G) →ₗ[F] v.ker) (y : B.Lift v) :
    f.symm (B.move v G L y) = A.move v G L (f.symm y) := by
  apply f.injective
  rw [f.apply_symm_apply,comm,f.apply_symm_apply]

include comm in
/-- Both sides of a tagged comparison lose height. In height zero the
empty value tuple is independent, so there are no unmatched labels. -/
theorem remainder_stratification (surj : Function.Surjective v) (d : v.ker) (hd : d ≠ 0)
    {P : ∀ n, Set (Fin n → V) → Prop}
    (cut : ∀ {k l} (p : Fin l → ValuePivot G k) (D) (i), P _ D → P _ (firstPivot p D i))
    (sat : RealizesAffineAvoidance G P) (i : A.Tag) (maximal : ∀ j, B.height j ≤ A.height i)
    (definable : P _ {z | ∃ hz : z ∈ A.domain i,
      ¬ ∃ b, WholeMatch (A.label v) (B.label v) f ⟨i,z,hz⟩ b}) :
    ∃ (l : ℕ) (pieces : Fin l → IndependentPiece P G (A.height i)),
      (∀ t, (pieces t).rank < A.height i) ∧
      {z | ∃ hz : z ∈ A.domain i, ¬ ∃ b, WholeMatch (A.label v) (B.label v) f ⟨i,z,hz⟩ b} =
        ⋃ t, (pieces t).support ∧
      Pairwise (fun t u => Disjoint (pieces t).support (pieces u).support) := by
  apply unmatched_stratification cut sat definable
  rintro z ⟨hz,missing⟩
  exact unmatched_dependent v G f comm surj d hd ⟨i,z,hz⟩ maximal missing

end FiberFamily
end GeneralizedEuler.Section4
