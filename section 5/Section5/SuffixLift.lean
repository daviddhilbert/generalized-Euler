module

public import Section5.VerticalImages

/-! Lift a tail transformation while keeping the head coordinate fixed.
The head leading term is read from a retained tag throughout. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2

variable {K : Type*} [Field K] (O : ValuationSubring K)
  {X Y Q W : Type*}

/-- The tail carries the range constraint on the fixed head coordinate.
Keeping this head tag allows any tail preparation to lift. -/
theorem suffixLift_image (T : X → Y) (A : Set X)
    (headIn : X → RV0 O) (headOut : Y → RV0 O)
    (preserves : ∀ x ∈ A, headOut (T x) = headIn x) :
    (Prod.map T (id : K → K)) '' {p : X × K | p.1 ∈ A ∧ rv O p.2 = headIn p.1} =
      {p : Y × K | p.1 ∈ T '' A ∧ rv O p.2 = headOut p.1} := by
  ext p
  rcases p with ⟨y, z⟩
  constructor
  · rintro ⟨⟨x,t⟩, ⟨hx,ht⟩, he⟩
    obtain ⟨hy, htz⟩ := Prod.mk.inj he
    change T x = y at hy
    change t = z at htz
    subst t
    exact ⟨⟨x,hx,hy⟩, ht.trans ((preserves x hx).symm.trans (congrArg headOut hy))⟩
  · rintro ⟨⟨x,hx,rfl⟩, hz⟩
    exact ⟨(x,z), ⟨hx, hz.trans (preserves x hx)⟩, rfl⟩

/-- A restriction or output test determined by the prepared tail label
stays determined by the full label after restoring the head coordinate. -/
theorem suffixLift_contracts (T : X → Y) (label : Y → Q) (A : Set X)
    (f : X → W) (descend : Q → W)
    (hf : ∀ x ∈ A, f x = descend (label (T x))) :
    ∀ p q : X × K, p.1 ∈ A → q.1 ∈ A →
      (label (T p.1), rv O p.2) = (label (T q.1), rv O q.2) → f p.1 = f q.1 := by
  intro p q hp hq he
  rw [hf _ hp, hf _ hq]
  exact congrArg descend (congrArg Prod.fst he)

end GeneralizedEuler.Section5
