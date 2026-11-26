module

public import Section5.DefinableRelations

/-! The transported focus graph for simultaneous preparation is a
composition of fixed-base graphs followed by a check of the source label. -/

public section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 FirstOrder

universe z

variable {L : Language} {E : Type*} {X : TCsort → Type z}
  {M : SortedStructure L E X} {S : SortedSubstructure M}
  {U V P Q : TCsort → Type}

/-- Move from a source label to a target label via an old source point,
choose the target focus, and take its inverse image. The last label
check selects the source fiber containing that inverse image. -/
theorem paired_focus_graph_definable
    [Finite (U .vf)] [Finite (U .rv)] [Finite (V .vf)] [Finite (V .rv)]
    [Finite (Q .vf)] [Finite (Q .rv)]
    (p : SortedAssignment X U → SortedAssignment X P)
    (q : SortedAssignment X V → SortedAssignment X Q)
    (F : SortedAssignment X U → SortedAssignment X V → Prop)
    (targetFocus : SortedAssignment X Q → SortedAssignment X V → Prop)
    (defP : DefinableRelation M S.carrier (fun a b => p a = b))
    (defQ : DefinableRelation M S.carrier (fun a b => q a = b))
    (defF : DefinableRelation M S.carrier F)
    (defFocus : DefinableRelation M S.carrier targetFocus) :
    DefinableRelation M S.carrier
      (fun u x => p x = u ∧ ∃ a b y, p a = u ∧ F a b ∧ targetFocus (q b) y ∧ F x y) := by
  have h := ((((defP.transpose.comp defF).comp defQ).comp defFocus).comp defF.transpose)
  have h' : DefinableRelation M S.carrier (fun u x => p x = u ∧
      ∃ y, (∃ l, (∃ b, (∃ a, p a = u ∧ F a b) ∧ q b = l) ∧ targetFocus l y) ∧ F x y) :=
    SortedDefinableOver.inter defP.transpose h
  apply h'.congr
  intro u x
  constructor
  · rintro ⟨hp,y,⟨_,⟨b,⟨a,ha,hF⟩,rfl⟩,hFocus⟩,hBack⟩
    exact ⟨hp,a,b,y,ha,hF,hFocus,hBack⟩
  · rintro ⟨hp,a,b,y,ha,hF,hFocus,hBack⟩
    exact ⟨hp,y,⟨q b,⟨b,⟨a,ha,hF⟩,rfl⟩,hFocus⟩,hBack⟩

/-- Since the old bijection contracts to the labels, the target label
used in the composition is independent of the source witness. -/
theorem paired_focus_graph_single_valued {A B R T : Type*}
    (p : A → R) (q : B → T) (e : A ≃ B)
    (targetFocus : T → B → Prop)
    (contract : ∀ a b, p a = p b → q (e a) = q (e b))
    (unique : ∀ t y y', targetFocus t y → targetFocus t y' → y = y')
    {r : R} {x x' : A}
    (h : p x = r ∧ ∃ a, p a = r ∧ targetFocus (q (e a)) (e x))
    (h' : p x' = r ∧ ∃ a, p a = r ∧ targetFocus (q (e a)) (e x')) :
    x = x' := by
  obtain ⟨_,a,ha,ha'⟩ := h
  obtain ⟨_,b,hb,hb'⟩ := h'
  have eq := contract a b (ha.trans hb.symm)
  exact e.injective (unique (q (e b)) _ _ (eq ▸ ha') hb')

end GeneralizedEuler.Section5
