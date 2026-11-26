module

public import Section4.SimultaneousBoxRanks
public import Section4.DefinableValueFrames
import all Section4.ScaleAvoidance

/-! The point, bounded interval and ray factors of a padded box. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open FirstOrder Set
variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module F V] [IsStrictOrderedModule F V]

inductive BoxSide (V : Type*) where
  | point
  | bounded (width : V)
  | ray

def BoxSide.domain : BoxSide V → Set V
  | .point => {0}
  | .bounded b => Ioo 0 b
  | .ray => Ioi 0

def BoxSide.survives (H : Submodule F V) : BoxSide V → Prop
  | .point => False
  | .bounded b => b ∉ H
  | .ray => True

theorem BoxSide.vanishes {a x : V} (D : BoxSide V) (hx : x ∈ D.domain)
    (small : ¬ D.survives (scaleSpace F a)) : x ∈ scaleSpace F a := by
  cases D with
  | point => exact (Set.mem_singleton_iff.mp hx) ▸ (scaleSpace F a).zero_mem
  | bounded b =>
    have h : b ∈ scaleSpace F a := Classical.not_not.mp small
    exact scaleSpace_mono F h (scaleSpace_interval F hx.1.le hx.2.le)
  | ray => exact (small trivial).elim

/-- Unary saturation is required over the original base enlarged by
finitely many previously chosen coordinates. -/
def UnaryValueSaturation (J : Language) [J.Structure V] (A : Set V) : Prop :=
  ∀ Δ : Set (J[[A]].Formula Unit),
    (∀ fs : Finset (J[[A]].Formula Unit), (↑fs : Set _) ⊆ Δ →
      ∃ x : Unit → V, ∀ φ ∈ fs, φ.Realize x) →
    ∃ x : Unit → V, ∀ φ ∈ Δ, φ.Realize x

omit [IsStrictOrderedRing F] [IsStrictOrderedModule F V] in
/-- Only the ordinary ordered-vector-space operations enter the type
used for avoiding tubes. -/
theorem scale_tube_definable {J : Language} [J.Structure V] (B : Submodule F V)
    (leDef : (B : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})
    (a : V) (ha : a ∈ B) (g : B) (c : F) :
    (B : Set V).Definable J (scaleTube F a g.val c) := by
  let width := |c| • |a|
  have ab : |a| ∈ B := by rcases abs_choice a with eq|eq <;> rw [eq]; exact ha; exact B.neg_mem ha
  have wb : width ∈ B := B.smul_mem _ ab
  let left := g.val - width
  let right := g.val + width
  have l := J.definableFun_const Unit (B.sub_mem g.property wb)
  have r := J.definableFun_const Unit (B.add_mem g.property wb)
  have var : (B : Set V).DefinableFun J (fun x : Unit → V => x ()) := Set.DefinableFun.proj J
  have cmp {u v : (Unit → V) → V} (hu : (B : Set V).DefinableFun J u)
      (hv : (B : Set V).DefinableFun J v) : (B : Set V).Definable J {x | u x ≤ v x} := by
    let pack (x : Unit → V) := ![u x,v x]
    have hd : (B : Set V).DefinableMap J pack := by intro i; fin_cases i <;> assumption
    exact leDef.preimage_map hd
  convert (cmp l var).inter (cmp var r) using 1
  ext x; change |x () - g.val| ≤ width ↔ g.val - width ≤ x () ∧ x () ≤ g.val + width
  rw [abs_le]
  constructor <;> rintro ⟨h,h'⟩ <;> constructor <;> grind


variable {I T : Type*} [Fintype I] {J : Language} [J.Structure V]

/-- Every box contains a single tuple attaining all the rank bounds.
The preceding scale is zero at the smallest width and the largest listed
scale for a ray. Padding contributes no independent coordinates. -/
theorem box_has_simultaneous_ranks (G : Submodule F V) (D : I → BoxSide V) (threshold : T → V)
    (prev : I → V) (inBase : ∀ i, prev i ∈ G)
    (leDef : (G : Set V).Definable J {x : Fin 2 → V | x 0 ≤ x 1})
    (dom : ∀ i, (G : Set V).Definable J {x : Unit → V | x () ∈ (D i).domain})
    (step : V) (positive : 0 < step)
    (width : ∀ i b, D i = .bounded b → 0 < b ∧ b ∉ scaleSpace F (prev i))
    (nested : ∀ i j, (D i).survives (scaleSpace F (threshold j)) →
      scaleSpace F (threshold j) ≤ scaleSpace F (prev i))
    (sat : ∀ s : Finset V, UnaryValueSaturation J (↑(G ⊔ Submodule.span F (s : Set V)) : Set V)) :
    ∃ x : I → V, (∀ i, x i ∈ (D i).domain) ∧ ∀ j,
      Module.finrank F (quotientTupleSpan (G ⊔ scaleSpace F (threshold j)) x) =
        Nat.card {i // (D i).survives (scaleSpace F (threshold j))} := by
  classical
  let active i j := (D i).survives (scaleSpace F (threshold j))
  have choosePoint (i : I) (s : Finset V) : ∃ y ∈ (D i).domain, (∃ j, active i j) →
      y ∉ (G ⊔ Submodule.span F (s : Set V)) ⊔ scaleSpace F (prev i) := by
    let B := G ⊔ Submodule.span F (s : Set V)
    have incl : G ≤ B := le_sup_left
    have take (finite : ∀ cuts : Finset (B × F), ∃ y ∈ (D i).domain,
        ∀ p ∈ cuts, |p.2| • |prev i| < |y - p.1.val|) := realize_outside_scale B (prev i) (D i).domain
      ((dom i).mono incl) (scale_tube_definable B (leDef.mono incl) (prev i) (incl (inBase i))) (sat s) finite
    cases eq : D i with
    | point =>
      refine ⟨0,by simp [BoxSide.domain],?_⟩
      rintro ⟨j,h⟩; simp [active,eq,BoxSide.survives] at h
    | bounded b =>
      obtain ⟨hb,outside⟩ := width i _ eq
      obtain ⟨y,hy,avoid⟩ := take (fun cuts => by
        simpa [eq,BoxSide.domain] using bounded_finite_scale_avoidance B hb outside cuts)
      exact ⟨y,eq ▸ hy,fun _ => avoid⟩
    | ray =>
      obtain ⟨y,hy,avoid⟩ := take (fun cuts => by
        let pack (p : B × F) : V × F := (p.1.val,p.2)
        obtain ⟨x,hx,miss⟩ := ray_avoid_finite_tubes (a := prev i) positive (cuts.image pack)
        exact ⟨x,by simpa [eq,BoxSide.domain] using hx,fun p hp => miss (pack p) (Finset.mem_image.mpr ⟨p,hp,rfl⟩)⟩)
      exact ⟨y,eq ▸ hy,fun _ => avoid⟩
  obtain ⟨x,hx,ind⟩ := independent_box_coordinates G (fun j => scaleSpace F (threshold j))
    (fun i => scaleSpace F (prev i)) active (fun i => (D i).domain) nested choosePoint
  refine ⟨x,hx,fun j => ?_⟩
  let large : Set I := {i | active i j}
  rw [Nat.card_eq_fintype_card]
  exact box_rank_attained _ x large (fun i miss => Submodule.mem_sup_right ((D i).vanishes (hx i) miss)) (ind j)

end GeneralizedEuler.Section4
