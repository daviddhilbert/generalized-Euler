module

public import Section4.AnnulusWidths
public import Section4.ValueScissors
import all Section4.BoxScaleProfiles
import all Section4.ValueBoxes
import all Section4.AnnulusWidths
import all Section4.IntervalScaleBijection

/-! The widths of a single bounded value box are recovered, with
multiplicity, from the ranks attained in the quotients by the base and
each scale. A width pairing gives a fixed-base definable box bijection. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set ValueObject
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]
  {I N : Type*} [Fintype I] [Fintype N] {J : Language} [J.Structure V]

def boundedBox (a : I → V) : Set (I → V) := {x | ∀ i, x i ∈ Ioo 0 (a i)}

def attainedWidthRanks (G : Submodule F V) (a : I → V) (c : V) : Set ℕ :=
  (fun x => Module.finrank F (quotientTupleSpan (G ⊔ scaleSpace F c) x)) '' boundedBox a

theorem widthTail_isGreatest (G : Submodule F V) (a : I → V) (ha : ∀ i, 0 < a i)
    (c : V) (old : c ∈ G) (nonneg : 0 ≤ c) (step : V) (pos : 0 < step)
    (leDef : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})
    (dom : ∀ i, (G : Set V).Definable J {x : Unit → V | x () ∈ Ioo 0 (a i)})
    (sat : ∀ fs : Finset V, UnaryValueSaturation J (↑(G ⊔ Submodule.span F (fs : Set V)) : Set V)) :
    IsGreatest (attainedWidthRanks G a c) (widthTail (F := F) a c) := by
  let D i := BoxSide.bounded (a i)
  let t (_ : Unit) := c
  obtain ⟨x,hx,hits⟩ := box_counts_attained G D t (fun _ => old) (fun _ => nonneg) leDef dom step pos
    (fun i b e => BoxSide.bounded.inj e ▸ ha i) sat
  refine ⟨⟨x,hx,congrFun hits ()⟩,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  exact box_tuple_profile_le G D t y hy ()

theorem bounded_widths_of_rank_sets (G : Submodule F V) (a : I → V) (b : N → V)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (ba : ∀ i, a i ∈ G) (bb : ∀ j, b j ∈ G)
    (step : V) (pos : 0 < step)
    (leDef : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})
    (da : ∀ i, (G : Set V).Definable J {x : Unit → V | x () ∈ Ioo 0 (a i)})
    (db : ∀ i, (G : Set V).Definable J {x : Unit → V | x () ∈ Ioo 0 (b i)})
    (sat : ∀ fs : Finset V, UnaryValueSaturation J (↑(G ⊔ Submodule.span F (fs : Set V)) : Set V))
    (eq : ∀ c ∈ G, 0 ≤ c → attainedWidthRanks G a c = attainedWidthRanks G b c) :
    ∃ e : I ≃ N, ∀ i, scaleSpace F (a i) = scaleSpace F (b (e i)) := by
  apply pair_widths_of_counts G a b ha hb ba bb
  intro c hc cp
  have left := widthTail_isGreatest G a ha c hc cp step pos leDef da sat
  rw [eq c hc cp] at left
  exact left.unique (widthTail_isGreatest G b hb c hc cp step pos leDef db sat)

omit [LinearOrder F] [IsStrictOrderedRing F] [IsOrderedAddMonoid V] [IsStrictOrderedModule F V] in
theorem boundedBox_definable (G : Submodule F V) (a : I → V)
    (dom : ∀ i, (G : Set V).Definable J {x : Unit → V | x () ∈ Ioo 0 (a i)}) :
    (G : Set V).Definable J (boundedBox a) := by
  convert Set.definable_iInter_of_finite (fun i => (dom i).preimage_comp (fun _ : Unit => i)) using 1
  ext x; simp [boundedBox]

theorem paired_widths_box_bijection (G : Submodule F V) (a : I → V) (b : N → V)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (ba : ∀ i, a i ∈ G) (bb : ∀ j, b j ∈ G)
    (lang : ValueLanguage (J := J) G) (leDef : ∀ t ∈ G, (G : Set V).Definable J {x : Unit → V | x () ≤ t})
    (da : (G : Set V).Definable J (boundedBox a))
    (e : I ≃ N) (scales : ∀ i, scaleSpace F (a i) = scaleSpace F (b (e i))) :
    ∃ f : boundedBox a ≃ boundedBox b, (G : Set V).Definable J
      {w : I ⊕ N → V | ∃ x : boundedBox a, x.val = w ∘ Sum.inl ∧ (f x).val = w ∘ Sum.inr} := by
  choose q images maps using fun i => comparable_widths_definable G lang leDef (ba i) (bb (e i)) (ha i) (hb (e i))
    ((scaleSpace_le_iff F).mp (scales i).le) ((scaleSpace_le_iff F).mp (scales i).ge)
  let f (x : I → V) (j : N) := q (e.symm j) (x (e.symm j))
  have inj : Function.Injective f := by
    intro x y h; funext i
    exact (q i).injective (by simpa [f] using congrFun h (e i))
  have image : f '' boundedBox a = boundedBox b := by
    ext y; constructor
    · rintro ⟨x,hx,rfl⟩ j
      obtain ⟨i,rfl⟩ := e.surjective j
      have := (images i) ▸ Set.mem_image_of_mem (q i) (hx i)
      simpa [f] using this
    · intro hy
      have pre i : y (e i) ∈ (q i) '' Ioo 0 (a i) := (images i).symm ▸ hy (e i)
      choose x hx eq using pre
      exact ⟨x,hx,funext fun j => by simpa [f] using eq (e.symm j)⟩
  let equiv := (Equiv.Set.imageOfInjOn f (boundedBox a) inj.injOn).trans (Set.equivOfEq image)
  have defMap : (G : Set V).DefinableMap J f := fun j =>
    (maps (e.symm j)).comp (g := fun x _ => x (e.symm j)) (fun _ => Set.DefinableFun.proj J)
  refine ⟨equiv,?_⟩
  convert graph_of_map f defMap _ da using 1
  ext w
  exact ⟨fun ⟨x,h,z⟩ => ⟨h ▸ x.property,h ▸ z⟩,fun ⟨h,z⟩ => ⟨⟨_,h⟩,rfl,z⟩⟩

end GeneralizedEuler.Section4
