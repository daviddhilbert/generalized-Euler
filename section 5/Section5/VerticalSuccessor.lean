module

public import Section5.DescendedVerticalGraph
public import Section5.SuffixLift

/-! Assembly of the three maps in a field-arity successor step.
The first tail map prepares center differences. The second tail map
prepares the relation with the head history as an auxiliary label. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 UnaryPreparation

variable {K : Type*} [Field K] {O : ValuationSubring K} {H X Y Z T : Type*}
  (P : X → UnaryPreparation O H) (firstTail : X → Y)
  (lastTail : Y × H → Z)

/-- A head translation between two tail maps. The second tail map
receives the complete head history and leaves the head field value fixed. -/
@[expose] def verticalSuccessorMap (p : X × K) : Z × K :=
  (lastTail (firstTail p.1, (P p.1).label p.2), ((P p.1).map p.2).1)

theorem verticalSuccessorMap_injective
    (hfirst : Function.Injective firstTail) (hlast : Function.Injective lastTail) :
    Function.Injective (verticalSuccessorMap P firstTail lastTail) := by
  rintro ⟨b,x⟩ ⟨b',x'⟩ he
  have h : lastTail (firstTail b, (P b).label x) = lastTail (firstTail b', (P b').label x') :=
    congrArg Prod.fst he
  obtain ⟨hb, ht⟩ := Prod.mk.inj (hlast h)
  have hbb := hfirst hb
  subst b'
  have hx : ((P b).map x).1 = ((P b).map x').1 := congrArg Prod.snd he
  exact Prod.ext rfl ((P b).map_injective (Prod.ext hx ht))

/-- The descended test contains the head history and the first prepared
tail coordinates. It no longer contains a head field variable. -/
@[expose] def succeededTailTest (G : Set (X × K × T)) (s : T) : Set (Y × H) :=
  {p | ∃ b x, firstTail b = p.1 ∧ (P b).label x = p.2 ∧ (b,x,s) ∈ G}

/-- The image for one output test is the lift of the prepared tail
relation along the retained head leading term. The same proof handles
every output test using the same maps. -/
theorem verticalSuccessor_image
    (G : Set (X × K × T))
    (hG : ∀ b x y s, (P b).label x = (P b).label y → ((b,x,s) ∈ G ↔ (b,y,s) ∈ G))
    (headLead : Z → RV0 O)
    (hlead : ∀ b t, headLead (lastTail (firstTail b,t)) = (P b).lead t)
    (s : T) :
    verticalSuccessorMap P firstTail lastTail '' {p | (p.1,p.2,s) ∈ G} =
      {q | q.1 ∈ lastTail '' succeededTailTest P firstTail G s ∧ rv O q.2 = headLead q.1} := by
  ext q
  rcases q with ⟨z,y⟩
  constructor
  · rintro ⟨⟨b,x⟩, hx, he⟩
    obtain ⟨hz, hy⟩ := Prod.mk.inj he
    change lastTail (firstTail b, (P b).label x) = z at hz
    change ((P b).map x).1 = y at hy
    refine ⟨⟨(firstTail b, (P b).label x), ⟨b,x,rfl,rfl,hx⟩, hz⟩, ?_⟩
    rw [← hz, hlead, ← hy]
    exact (P b).leading x
  · rintro ⟨⟨⟨u,t⟩, ⟨b,x,hb,ht,hx⟩, hz⟩, hy⟩
    change firstTail b = u at hb
    change lastTail (u,t) = z at hz
    subst u
    subst z
    rw [hlead] at hy
    let w := y + (P b).offset t
    have hw : (P b).label w = t :=
      ((P b).label_eq_iff (x := x) (y := w)).2 (by simpa [w, ht] using hy) |>.trans ht
    refine ⟨(b,w), (hG b w x s (hw.trans ht.symm)).2 hx, ?_⟩
    have hy' : ((P b).map w).1 = y := by simp [UnaryPreparation.map, w, hw]
    exact Prod.ext (congrArg (fun a => lastTail (firstTail b,a)) hw) hy'

/-- Preparing the descended relation gives full output-label fibers in
the combined preparation, provided the retained lead is a tail label. -/
theorem verticalSuccessor_pullback {Q : Type*} (tailLabel : Z → Q)
    (G : Set (X × K × T))
    (hG : ∀ b x y s, (P b).label x = (P b).label y → ((b,x,s) ∈ G ↔ (b,y,s) ∈ G))
    (headLead : Q → RV0 O)
    (hlead : ∀ b t, headLead (tailLabel (lastTail (firstTail b,t))) = (P b).lead t)
    (labels : T → Set Q)
    (htail : ∀ s, lastTail '' succeededTailTest P firstTail G s = tailLabel ⁻¹' labels s)
    (s : T) :
    verticalSuccessorMap P firstTail lastTail '' {p | (p.1,p.2,s) ∈ G} =
      {q | tailLabel q.1 ∈ labels s ∧ rv O q.2 = headLead (tailLabel q.1)} := by
  rw [verticalSuccessor_image P firstTail lastTail G hG (headLead ∘ tailLabel) hlead s, htail]
  rfl

end GeneralizedEuler.Section5
