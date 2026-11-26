module

public import Section4.BarycentricValueFibers
public import Section4.ArbitraryBoxUnions
import all Section4.ArbitraryBoxUnions
import all Section4.ValueBoxProducts
import all Section4.ValueScissors
import all Section4.BarycentricValueFibers
import all Section4.BoundedIntervalScissors
import all Section4.BoundedValueBoxes

/-! The fiber of a normalized simplicial cone has a free positive
coefficient on each vertical ray and one positive sum fiber for each
parameter ray. Its box occupies the original ambient degree. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set ValueObject PaddedBox
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {J : Language} [J.Structure V] {G : Submodule F V} {k : ℕ}

structure ConeFiber (G : Submodule F V) (k : ℕ) where
  rays : ℕ
  groups : ℕ
  dim : Fin groups → ℕ
  width : Fin groups → G
  positive : ∀ b, 0 < (width b : V)
  padding : ℕ
  layout : Fin k ≃ Fin padding ⊕ (Fin rays ⊕ ((b : Fin groups) × Fin (dim b)))

namespace ConeFiber
variable (c : ConeFiber G k)
abbrev Coeff := Fin c.rays ⊕ ((b : Fin c.groups) × Fin (c.dim b + 1))

def domain : Set (c.Coeff → V) :=
  {x | (∀ r, 0 < x (.inl r)) ∧ ∀ b, (fun i => x (.inr ⟨b,i⟩)) ∈ sumFiber (c.width b : V)}

def axis (i : Fin k) : BoxSide V := match c.layout i with
  | .inl _ => .point
  | .inr (.inl _) => .ray
  | .inr (.inr ⟨b,_⟩) => .bounded (c.width b)

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem axis_widths (i : Fin k) (t : V) (h : c.axis i = .bounded t) : t ∈ G ∧ 0 < t := by
  unfold axis at h
  split at h <;> cases h
  exact ⟨(c.width _).property,c.positive _⟩

def boxMap (x : c.Coeff → V) (i : Fin k) : V := match c.layout i with
  | .inl _ => 0
  | .inr (.inl r) => x (.inl r)
  | .inr (.inr ⟨b,j⟩) => sumFiberMap (fun t => x (.inr ⟨b,t⟩)) j

omit [LinearOrder F] [IsStrictOrderedRing F] [IsStrictOrderedModule F V] in
theorem box_injOn : InjOn c.boxMap c.domain := by
  intro x hx y hy eq
  funext t
  rcases t with r | ⟨b,j⟩
  · simpa [boxMap] using congrFun eq (c.layout.symm (.inr (.inl r)))
  · apply congrFun (sumFiberMap_injOn _ (hx.2 b) (hy.2 b) _) j
    funext i
    simpa [boxMap] using congrFun eq (c.layout.symm (.inr (.inr ⟨b,i⟩)))

omit [IsStrictOrderedModule F V] in
theorem box_image : c.boxMap '' c.domain = coordinateBox (fun i => unarySide (c.axis i)) := by
  classical
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩ i
    cases tag : c.layout i with
    | inl p => simp [boxMap,axis,tag,unarySide]; rfl
    | inr t =>
      rcases t with r|⟨b,j⟩
      · simpa [axis,tag,boxMap,unarySide,upperRay] using hx.1 r
      · have law := (sumFiberMap_image (F := F) (n := c.dim b) (c.width b : V) (c.positive b)) ▸
            (Set.mem_image_of_mem sumFiberMap (hx.2 b))
        exact (show _ from by simpa [boxMap,axis,tag,unarySide,intervalPiece] using law j)
  · intro hy
    let chunk (b : Fin c.groups) (j : Fin (c.dim b)) := y (c.layout.symm (.inr (.inr ⟨b,j⟩)))
    have bounded b : chunk b ∈ boundedBox (fun _ : Fin (c.dim b) => (c.width b : V)) := by
      intro j
      simpa [chunk,axis,unarySide,intervalPiece] using hy (c.layout.symm (.inr (.inr ⟨b,j⟩)))
    have lift b := (sumFiberMap_image (F := F) (n := c.dim b) (c.width b : V) (c.positive b)).symm ▸ bounded b
    choose u hu eu using lift
    let x : c.Coeff → V := Sum.elim (fun r => y (c.layout.symm (.inr (.inl r)))) (fun t => u t.1 t.2)
    refine ⟨x,⟨?_,hu⟩,?_⟩
    · intro r
      simpa [x,axis,unarySide,upperRay] using hy (c.layout.symm (.inr (.inl r)))
    · funext i
      obtain ⟨t,rfl⟩ := c.layout.symm.surjective i
      rcases t with p|r|⟨b,j⟩
      · have zero := hy (c.layout.symm (.inl p))
        simpa [boxMap,axis,unarySide] using (congrFun (show (fun _ : Fin 1 => y _) = 0 from by simpa [axis,unarySide] using zero) 0).symm
      · simp [boxMap,x]
      · simpa [boxMap,x,chunk] using congrFun (eu b) j

variable (L : BoxLanguage (J := J) G) (order : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
include L order in
theorem domain_definable : (G : Set V).Definable J c.domain := by
  have ray r := L.ray.preimage_comp (fun _ : Fin 1 => (Sum.inl r : c.Coeff))
  have group b := (sumFiber_definable G L.arithmetic order (n := c.dim b) _ (c.width b).property).preimage_comp
    (fun i => (Sum.inr ⟨b,i⟩ : c.Coeff))
  convert (Set.definable_iInter_of_finite ray).inter (Set.definable_iInter_of_finite group) using 1
  ext x; simp [domain,upperRay,Function.comp_def]

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
include L order in
theorem boxMap_definable : (G : Set V).DefinableMap J c.boxMap := by
  intro i
  unfold boxMap
  split
  · exact J.definableFun_const _ G.zero_mem
  · exact Set.DefinableFun.proj J
  · rename_i b j _
    exact ((sumFiberMap_definable G L.arithmetic order (c.dim b)) j).comp (g := fun (x : c.Coeff → V) (t : Fin (c.dim b + 1)) => x (Sum.inr ⟨b,t⟩)) (fun _ => Set.DefinableFun.proj J)

omit [IsStrictOrderedModule F V] in
include order in
theorem image_class (f : (c.Coeff → V) → Fin k → V) (hf : (G : Set V).DefinableMap J f) (inj : InjOn f c.domain) :
    pieceClass _ (image_of_map f hf _ (c.domain_definable L order)) =
      presentationValue L (⟨1,fun _ => c.axis,fun _ => c.axis_widths⟩ : Presentation G k) := by
  have compare := pieceClass_images_of_finite f c.boxMap hf (c.boxMap_definable L order) _
    (c.domain_definable L order) inj c.box_injOn
  rw [compare]
  simp only [presentationValue,Fin.sum_univ_one]
  congr 1
  exact c.box_image

end ConeFiber
end GeneralizedEuler.Section4
