module

public import Section5.FiberProductTests
public import Section5.PositionedCellClassification
import all Section3.AffineSlopes

/-! A tagged positioned family can have point, constant-disc, and
affine-disc leaves. A fiber which is not a product must be a
balanced affine disc with the strict radius inequality. -/

public section

noncomputable section

namespace GeneralizedEuler.Section5

open GeneralizedEuler.Section2 GeneralizedEuler.Section3 GeneralizedEuler.Section4 FirstOrder

universe z

variable {K : Type z} [Field K] {O : ValuationSubring K}
  {L : Language} {E : Type*}
  {M : SortedStructure L E (CanonicalSort O)} {S : SortedSubstructure M} {k : ℕ}

local notation "Z" => CanonicalSort O

namespace RetainedFieldFamily

variable (A : RetainedFieldFamily M S 2 k)

@[expose] def pairFiber (q : A.tags → RV0 O) : Set (K × K) :=
  {p | ((Fin.cases p.1 (fun _ => p.2) : Fin 2 → K),q) ∈ A.carrier}

@[expose] def firstDomain (q : A.tags → RV0 O) : Set K :=
  {x | (x,q) ∈ A.factorProjection 0}

theorem productFiber_of_pairFiber_eq (q : A.tags → RV0 O) (D F : Set K)
    (e : A.pairFiber q = D ×ˢ F) : q ∈ A.productFibers := by
  have tuple (b : Fin 2 → K) : (Fin.cases (b 0) (fun _ => b 1) : Fin 2 → K) = b := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rw [Fin.eq_zero j]
    rfl
  have ge (x : Fin 2 → K) : (x,q) ∈ A.carrier ↔ x 0 ∈ D ∧ x 1 ∈ F := by
    have h : (x 0,x 1) ∈ A.pairFiber q ↔ (x,q) ∈ A.carrier := by
      change ((Fin.cases (x 0) (fun _ => x 1) : Fin 2 → K),q) ∈ A.carrier ↔ _
      rw [tuple]
    rw [e] at h
    exact h.symm
  intro b h₀ h₁
  obtain ⟨x,hx,ex⟩ := h₀
  obtain ⟨y,hy,ey⟩ := h₁
  have h₀ : b 0 ∈ D := by rw [← show x 0 = b 0 from ex]; exact ((ge x).1 hx).1
  have h₁ : b 1 ∈ F := by rw [← show y 1 = b 1 from ey]; exact ((ge y).1 hy).2
  exact (ge b).2 ⟨h₀,h₁⟩

theorem verticalCarrier_pairFiber (q : A.tags → RV0 O) (b : Fin 1 → K) (x : K) :
    (x,b,q) ∈ A.verticalCarrier ↔ (x,b 0) ∈ A.pairFiber q := by
  have eq : (Fin.cons x b : Fin 2 → K) = Fin.cases x (fun _ => b 0) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rw [Fin.eq_zero j]
    rfl
  change (Fin.cons x b,q) ∈ A.carrier ↔ (Fin.cases x (fun _ => b 0),q) ∈ A.carrier
  rw [eq]

theorem swapped_verticalCarrier_pairFiber (q : A.tags → RV0 O) (b : Fin 1 → K) (x : K) :
    (x,b,q) ∈ (A.permuteVF (Equiv.swap 0 1)).verticalCarrier ↔ (b 0,x) ∈ A.pairFiber q := by
  let e := Equiv.swap (0 : Fin 2) 1
  let p : Fin 2 → K := Fin.cons x b
  have eq : p ∘ e.symm = Fin.cases (b 0) (fun _ => x) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change p (e 0) = b 0
      rw [show e 0 = 1 from Equiv.swap_apply_left _ _]
      rfl
    · rw [Fin.eq_zero j]
      change p (e 1) = x
      rw [show e 1 = 0 from Equiv.swap_apply_right _ _]
      rfl
  change (p ∘ e.symm,q) ∈ A.carrier ↔ (Fin.cases (b 0) (fun _ => x),q) ∈ A.carrier
  rw [eq]

theorem firstDomain_iff_pair (q : A.tags → RV0 O) (x : K) :
    x ∈ A.firstDomain q ↔ ∃ y, (x,y) ∈ A.pairFiber q := by
  constructor
  · rintro ⟨b,h,eq⟩
    have e : (Fin.cases x (fun _ => b 1) : Fin 2 → K) = b := by
      funext i
      refine Fin.cases eq.symm (fun j => ?_) i
      rw [Fin.eq_zero j]
      rfl
    exact ⟨b 1,by change (Fin.cases x (fun _ => b 1),q) ∈ A.carrier; rwa [e]⟩
  · rintro ⟨y,h⟩
    let b : Fin 2 → K := Fin.cases x (fun _ => y)
    exact ⟨b,h,rfl⟩

end RetainedFieldFamily

structure TaggedPositioningData (A : RetainedFieldFamily M S 2 k) where
  position : K → (A.tags → RV0 O) → K
  paradigm : (A.tags → RV0 O) → RV0 O
  positionDef : DefinableRelation M S.carrier (fun
    (a : SortedAssignment (CanonicalSort O) (MixedVariables 1 A.tags))
    (b : fieldAssignment 1 (CanonicalSort O)) => position (a .vf 0) (a .rv) = b .vf 0)
  paradigmDef : DefinableRelation M S.carrier (fun
    (a : SortedAssignment (CanonicalSort O) (RVVariables A.tags))
    (b : SortedAssignment (CanonicalSort O) (RVVariables (Fin 1))) => paradigm (a .rv) = b .rv 0)
  shapes : ∀ q, A.pairFiber q = positionedCell O (A.firstDomain q) (fun x => position x q) (paradigm q)

structure TaggedTwoCellGeometry (A : RetainedFieldFamily M S 2 k) extends TaggedPositioningData A where
  leaves : ∀ q, let D := A.firstDomain q; let f := fun x => position x q
    (∀ x ∈ D, ∀ y ∈ D, f x = f y) ∨
      ∃ (a b : K) (r s : O.ValueGroup) (u : RV O), r ≠ 0 ∧ s ≠ 0 ∧
        D = openDisc O a r ∧ f '' D = openDisc O b s ∧ RVAffineOn O D f u

namespace TaggedTwoCellGeometry

variable {A : RetainedFieldFamily M S 2 k} (C : TaggedTwoCellGeometry A)

theorem nonproduct_chart (q : A.tags → RV0 O) (bad : q ∉ A.productFibers) :
    ∃ (a b : K) (r s : O.ValueGroup) (u : RV O), r ≠ 0 ∧ s ≠ 0 ∧
      A.firstDomain q = openDisc O a r ∧ (fun x => C.position x q) '' A.firstDomain q = openDisc O b s ∧
      RVAffineOn O (A.firstDomain q) (fun x => C.position x q) u ∧ unsignedValue O (C.paradigm q) < s := by
  let D := A.firstDomain q
  let f (x : K) := C.position x q
  let t := C.paradigm q
  classical
  rcases C.leaves q with constant | ⟨a,b,r,s,u,hr,hs,domain,image,affine⟩
  · exfalso
    apply bad
    by_cases exist : D.Nonempty
    · obtain ⟨x,hx⟩ := exist
      have prod := constant_positioned_cell_product O D f (f x) t (fun y hy => constant y hy x hx)
      exact A.productFiber_of_pairFiber_eq q D _ ((C.shapes q).trans prod)
    · apply A.productFiber_of_pairFiber_eq q (∅ : Set K) ∅
      have empty : D = ∅ := Set.not_nonempty_iff_eq_empty.1 exist
      rw [C.shapes q,show A.firstDomain q = ∅ from empty]
      ext p
      simp [positionedCell]
  · refine ⟨a,b,r,s,u,hr,hs,domain,image,affine,?_⟩
    by_contra! large
    have ha : a ∈ D := by rw [show D = openDisc O a r from domain]; exact mem_openDisc_center O hr a
    have maps : Set.MapsTo f D (openDisc O b s) := fun x hx => image ▸ Set.mem_image_of_mem f hx
    have prod := positionedCell_product_of_radius O hs ha maps large
    exact bad (A.productFiber_of_pairFiber_eq q D _ ((C.shapes q).trans prod))

theorem position_injective_on_nonproduct (q : A.tags → RV0 O) (bad : q ∉ A.productFibers) :
    Set.InjOn (fun x => C.position x q) (A.firstDomain q) := by
  obtain ⟨_,_,_,_,u,_,_,_,_,affine,_⟩ := C.nonproduct_chart q bad
  intro x hx y hy e
  have h := affine x hx y hy
  rw [sub_eq_zero.2 e,map_zero] at h
  exact sub_eq_zero.1 ((rv_eq_zero_iff O).1 ((mul_eq_zero (M₀ := RV0 O)).1 h.symm |>.resolve_left WithZero.coe_ne_zero))

end TaggedTwoCellGeometry

end GeneralizedEuler.Section5
