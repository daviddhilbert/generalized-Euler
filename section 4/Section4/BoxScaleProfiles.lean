module

public import Section4.ValueBoxes
import all Section4.ValueBoxes
import all Section4.IntervalScales

/-! Intrinsic ranks of boxes for a finite list of nonnegative thresholds.
The largest surviving threshold is selected from the list over the same base. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open Set FirstOrder
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]

@[simp] theorem scaleSpace_zero : scaleSpace F (0 : V) = ⊥ := by
  ext x
  change (∃ c : F, 0 ≤ c ∧ |x| ≤ c • |(0:V)|) ↔ x = 0
  simp
  exact fun _ => ⟨0,le_rfl⟩

theorem preceding_box_scale {T : Type*} [Fintype T] (G : Submodule F V)
    (t : T → V) (old : ∀ j, t j ∈ G) (nonneg : ∀ j, 0 ≤ t j)
    (D : BoxSide V) (positive : ∀ b, D = .bounded b → 0 < b) :
    ∃ p ∈ G, (∀ b, D = .bounded b → b ∉ scaleSpace F p) ∧
      ∀ j, D.survives (scaleSpace F (t j)) → scaleSpace F (t j) ≤ scaleSpace F p := by
  classical
  let s := insert 0 (Finset.univ.image t |>.filter (fun a => D.survives (scaleSpace F a)))
  have zeroIn : (0:V) ∈ s := Finset.mem_insert_self _ _
  let p := s.max' ⟨0,zeroIn⟩
  have whereP := Finset.mem_insert.mp (s.max'_mem ⟨0,zeroIn⟩)
  have base : p ∈ G := by
    rcases whereP with h|h
    · change p = 0 at h; rw [h]; exact G.zero_mem
    · obtain ⟨j,_,e⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
      change t j = p at e; rw [← e]; exact old j
  refine ⟨p,base,?_,?_⟩
  · intro b eq
    rcases whereP with h|h
    · change p = 0 at h
      simpa [h] using (positive b eq).ne'
    · have survives := (Finset.mem_filter.mp h).2
      rw [eq] at survives
      exact survives
  · intro j active
    have incl : t j ∈ s := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j),active⟩)
    exact scaleSpace_mono F (scaleSpace_interval F (nonneg j) (s.le_max' _ incl))

variable {I T : Type*} [Fintype I] [Fintype T]
def boxScaleCounts (D : I → BoxSide V) (t : T → V) (j : T) := Nat.card {i // (D i).survives (scaleSpace F (t j))}

def boxTupleProfile (G : Submodule F V) (t : T → V) (x : I → V) (j : T) :=
  Module.finrank F (quotientTupleSpan (G ⊔ scaleSpace F (t j)) x)

omit [Fintype T] in
theorem box_tuple_profile_le (G : Submodule F V) (D : I → BoxSide V) (t : T → V) (x : I → V)
    (belongs : ∀ i, x i ∈ (D i).domain) :
    boxTupleProfile G t x ≤ boxScaleCounts (F := F) D t := by
  classical
  intro j
  let large : Set I := {i | (D i).survives (scaleSpace F (t j))}
  change Module.finrank F _ ≤ Nat.card large
  rw [Nat.card_eq_fintype_card]
  exact box_rank_bound _ x large (fun i h => Submodule.mem_sup_right ((D i).vanishes (belongs i) h))

theorem box_counts_attained {J : Language} [J.Structure V] (G : Submodule F V) (D : I → BoxSide V)
    (t : T → V) (old : ∀ j, t j ∈ G) (nonneg : ∀ j, 0 ≤ t j)
    (leDef : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})
    (dom : ∀ i, (G : Set V).Definable J {x : Unit → V | x () ∈ (D i).domain})
    (step : V) (pos : 0 < step) (width : ∀ i b, D i = .bounded b → 0 < b)
    (sat : ∀ s : Finset V, UnaryValueSaturation J (↑(G ⊔ Submodule.span F (s : Set V)) : Set V)) :
    ∃ x : I → V, (∀ i, x i ∈ (D i).domain) ∧ boxTupleProfile G t x = boxScaleCounts (F := F) D t := by
  choose p base w nested using fun i => preceding_box_scale G t old nonneg (D i) (width i)
  obtain ⟨x,hx,ranks⟩ := box_has_simultaneous_ranks G D t p base leDef dom step pos
    (fun i b eq => ⟨width i b eq,w i b eq⟩) nested sat
  exact ⟨x,hx,funext ranks⟩

end GeneralizedEuler.Section4
