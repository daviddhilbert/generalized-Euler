module

public import Section4.BoxScaleProfiles
public import Section4.LiftQuotientProfiles

/-! Comparing two presentations by padded boxes. A single image tuple
controls every threshold, so the inequality is coordinatewise. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open Set FirstOrder
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {I T : Type*} [Fintype I] [Fintype T] {J : Language} [J.Structure V]
  (G : Submodule F V) (t : T → V) (old : ∀ j, t j ∈ G) (nonneg : ∀ j, 0 ≤ t j)
  (leDef : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})
  (step : V) (pos : 0 < step)
  (sat : ∀ s : Finset V, UnaryValueSaturation J (↑(G ⊔ Submodule.span F (s : Set V)) : Set V))

def boxRankProfiles (D : I → BoxSide V) : Set (T → ℕ) :=
  boxTupleProfile G t '' {x | ∀ i, x i ∈ (D i).domain}

include old nonneg leDef pos sat in
theorem maximal_box_vectors {A B : Type*} (U : A → I → BoxSide V) (W : B → I → BoxSide V)
    (du : ∀ a i, (G : Set V).Definable J {x : Unit → V | x () ∈ (U a i).domain})
    (dw : ∀ b i, (G : Set V).Definable J {x : Unit → V | x () ∈ (W b i).domain})
    (wu : ∀ a i l, U a i = .bounded l → 0 < l) (ww : ∀ b i l, W b i = .bounded l → 0 < l)
    (equal : (⋃ a, boxRankProfiles G t (U a)) = ⋃ b, boxRankProfiles G t (W b)) :
    {p | Maximal (· ∈ Set.range (fun a => boxScaleCounts (F := F) (U a) t)) p} =
    {p | Maximal (· ∈ Set.range (fun b => boxScaleCounts (F := F) (W b) t)) p} := by
  have upper (D : I → BoxSide V) p (hp : p ∈ boxRankProfiles G t D) : p ≤ boxScaleCounts (F := F) D t := by
    obtain ⟨x,hx,rfl⟩ := hp
    exact box_tuple_profile_le G D t x hx
  have hits (D : I → BoxSide V) (hd : ∀ i, (G : Set V).Definable J {x : Unit → V | x () ∈ (D i).domain})
      (width : ∀ i l, D i = .bounded l → 0 < l) : boxScaleCounts (F := F) D t ∈ boxRankProfiles G t D :=
    box_counts_attained G D t old nonneg leDef hd step pos width sat
  exact maximal_box_ranks _ _ (fun a => upper (U a)) (fun b => upper (W b))
    (fun a => hits _ (du a) (wu a)) (fun b => hits _ (dw b) (ww b)) equal

omit [Fintype I] [Fintype T] in
/-- Read the profile set of a tagged box union directly from its labels.
The hypothesis on each tag merely specifies its set of unsigned tuples. -/
theorem box_union_profiles {A X : Type*} (tag : X → A) (coords : X → I → V) (boxes : A → I → BoxSide V)
    (presentation : ∀ a, coords '' {x | tag x = a} = {v | ∀ i, v i ∈ (boxes a i).domain}) :
    Set.range (fun x => boxTupleProfile G t (coords x)) = ⋃ a, boxRankProfiles G t (boxes a) := by
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    exact Set.mem_iUnion.mpr ⟨tag x,coords x,(presentation (tag x)) ▸ Set.mem_image_of_mem coords rfl,rfl⟩
  · rintro h
    obtain ⟨a,v,hv,e⟩ := Set.mem_iUnion.mp h
    obtain ⟨x,_,hx⟩ := (congrArg (v ∈ ·) (presentation a)).mpr hv
    exact ⟨x,(congrArg (boxTupleProfile G t) hx).trans e⟩

end GeneralizedEuler.Section4
