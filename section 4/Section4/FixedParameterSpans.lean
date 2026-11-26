module

public import Section4.TaggedFiberMatching
public import Section4.QuotientSpanProfiles
import all Section4.TaggedFiberMatching
import all Section4.FiberMatching

/-! Residue coordinates fixed by every shear can be included as tags.
A bijection may change these tags. It still preserves the whole space
spanned by the value coordinates, simultaneously in all larger quotients. -/
public section
namespace GeneralizedEuler.Section4.FiberFamily
variable {F V T : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup T] [Module F T]
  (v : T →ₗ[F] V) (G : Submodule F V)

@[expose] def withParameters (A : FiberFamily V) (P : Type*) : FiberFamily V where
  Tag := P × A.Tag
  height i := A.height i.2
  domain i := A.domain i.2

def parameterPoints (A : FiberFamily V) (P : Type*) : (A.withParameters P).Lift v ≃ P × A.Lift v where
  toFun x := (x.1.1,⟨x.1.2,x.2⟩)
  invFun x := ⟨(x.1,x.2.1),x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem spans_with_fixed_parameters {A B : FiberFamily V} {P Q : Type*}
    (f : P × A.Lift v ≃ Q × B.Lift v)
    (comm : ∀ L p x, f (p,A.move v G L x) = ((f (p,x)).1,B.move v G L (f (p,x)).2))
    (d : v.ker) (hd : d ≠ 0) (p : P) (x : A.Lift v) :
    ∀ H : Submodule F V, G ≤ H → quotientTupleSpan H (v ∘ x.2.val) =
      quotientTupleSpan H (v ∘ (f (p,x)).2.2.val) := by
  let a := parameterPoints v A P
  let b := parameterPoints v B Q
  let e := a.trans (f.trans b.symm)
  have equivariant : ∀ L z, e ((A.withParameters P).move v G L z) =
      (B.withParameters Q).move v G L (e z) := by
    intro L z
    exact congrArg b.symm (comm L z.1.1 ⟨z.1.2,z.2⟩)
  have eq := span_preserved v G e equivariant d hd (a.symm (p,x))
  exact fun _ le => quotientTupleSpan_of_le le eq

end GeneralizedEuler.Section4.FiberFamily
