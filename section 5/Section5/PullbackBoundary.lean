module

public import Section5.LiftBoundary

/-! Restricting an RV boundary to a union of whole leading-term fibers. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section3

variable {X U : Type*} (p : X → U) (A : Set U)

/-- The boundary inside a union of whole fibers is the ambient boundary
of the embedded set, viewed as a subset of the retained labels. -/
theorem rvBoundary_on_pullback (D : Set (p ⁻¹' A)) :
    rvBoundary (fun x : (p ⁻¹' A : Set X) => (⟨p x.val,x.property⟩ : A)) D =
      Subtype.val ⁻¹' rvBoundary p (Subtype.val '' D) := by
  ext a
  constructor
  · rintro ⟨⟨x,hx,hlabel⟩,y,hy,hn⟩
    refine ⟨⟨x.val,⟨x,hx,rfl⟩,congrArg Subtype.val hlabel⟩,
      y.val,congrArg Subtype.val hy,?_⟩
    rintro ⟨w,hw,he⟩
    exact hn ((Subtype.ext he) ▸ hw)
  · rintro ⟨⟨x,⟨x',hx,rfl⟩,he⟩,y,hy,hn⟩
    have hyA : y ∈ p ⁻¹' A := by
      change p y ∈ A
      rw [hy]
      exact a.property
    let y' : p ⁻¹' A := ⟨y,hyA⟩
    exact ⟨⟨x',hx,Subtype.ext he⟩,y',Subtype.ext hy,
      fun h => hn ⟨y',h,rfl⟩⟩

end GeneralizedEuler.Section5
