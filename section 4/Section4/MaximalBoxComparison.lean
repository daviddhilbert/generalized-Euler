module

public import Section4.BoxUnionComparison
public import Mathlib.Order.Preorder.Finite
import all Section4.BoxMultiplicity

/-! Restrict the positive box comparison to the common downward closure
of the maximal types. This also treats empty unions and unions having
no ray. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.BoxMultiplicity
variable {T M : Type*} [Fintype T] [PartialOrder T] [AddCommMonoid M]

private def restrictTypes (D : Set T) (s : Multiset T) (h : ∀ x ∈ s, x ∈ D) : Multiset D :=
  s.attach.map (fun x => ⟨x.val,h x.val x.property⟩)

omit [Fintype T] [PartialOrder T] in
private theorem restrict_weight (w : T → M) (D : Set T) (s : Multiset T) (h : ∀ x ∈ s, x ∈ D) :
    weight (fun x : D => w x.val) (restrictTypes D s h) = weight w s := by
  simp [weight,restrictTypes,Multiset.map_map,Multiset.attach_map_val']

omit [Fintype T] [PartialOrder T] in
private theorem mem_restrict (D : Set T) (s : Multiset T) (h : ∀ x ∈ s, x ∈ D) (x : D) :
    x ∈ restrictTypes D s h ↔ x.val ∈ s := by
  constructor
  · rintro hx
    obtain ⟨t,_,rfl⟩ := Multiset.mem_map.mp hx
    exact t.property
  · intro hx
    exact Multiset.mem_map.mpr ⟨⟨x.val,hx⟩,Multiset.mem_attach _ _,Subtype.ext rfl⟩

theorem compare_by_maximal_types (w : T → M) (p r : T) (ne : p ≠ r) (dim : T → ℕ) (face : T → T)
    (cut : ∀ q, q ≠ p ∧ q ≠ r → w q = w q + (w q + w (face q)))
    (lower : ∀ q, q ≠ p ∧ q ≠ r → dim (face q) < dim q)
    (below : ∀ q, q ≠ p ∧ q ≠ r → face q ≤ q)
    (extract : ∀ a b : T, a < b → ∃ rest : Multiset T,
      w b = w b + (w a + weight w rest) ∧ ∀ z ∈ rest, z ≤ b)
    (bounded geometric : M →+ ℤ) (bp : bounded (w p) = 1) (br : bounded (w r) = 0)
    (gp : geometric (w p) = 1) (gr : geometric (w r) = -1)
    (s t : Multiset T)
    (maximal : {q | Maximal (· ∈ s) q} = {q | Maximal (· ∈ t) q})
    (eb : bounded (weight w s) = bounded (weight w t))
    (eg : geometric (weight w s) = geometric (weight w t)) : weight w s = weight w t := by
  classical
  let dominated (u : Multiset T) x := ∃ b ∈ u, x ≤ b
  have dom (x : T) : dominated s x ↔ dominated t x := by
    have forward (a b : Multiset T) (eq : {q | Maximal (· ∈ a) q} = {q | Maximal (· ∈ b) q}) :
        dominated a x → dominated b x := by
      rintro ⟨y,hy,le⟩
      obtain ⟨z,yz,max⟩ := (Set.toFinite {q | q ∈ a}).exists_le_maximal hy
      have mz : Maximal (· ∈ b) z := (congrArg (z ∈ ·) eq).mp max
      exact ⟨z,mz.1,le.trans yz⟩
    exact ⟨forward s t maximal,forward t s maximal.symm⟩
  let D : Set T := {q | q=p ∨ q=r ∨ dominated s q}
  let P : D := ⟨p,.inl rfl⟩
  let R : D := ⟨r,.inr (.inl rfl)⟩
  have nPR : P ≠ R := fun e => ne (congrArg Subtype.val e)
  have reg {x : D} (h : x ≠ P ∧ x ≠ R) : x.val ≠ p ∧ x.val ≠ r :=
    ⟨fun eq => h.1 (Subtype.ext eq),fun eq => h.2 (Subtype.ext eq)⟩
  have old {x : D} (h : x ≠ P ∧ x ≠ R) : dominated s x.val :=
    (x.property.resolve_left (reg h).1).resolve_left (reg h).2
  have ds : ∀ x ∈ s, x ∈ D := fun x hx => .inr (.inr ⟨x,hx,le_rfl⟩)
  have dt : ∀ x ∈ t, x ∈ D := fun x hx => .inr (.inr ((dom x).mpr ⟨x,hx,le_rfl⟩))
  let F (x : D) : D := if h : x ≠ P ∧ x ≠ R then ⟨face x.val,by
    obtain ⟨b,hb,le⟩ := old h
    exact .inr (.inr ⟨b,hb,(below _ (reg h)).trans le⟩)⟩ else x
  have faceVal (x : D) (h : x ≠ P ∧ x ≠ R) : (F x).val = face x.val := by simp [F,h]
  let W (x : D) := w x.val
  have available (u : Multiset T) (du : ∀ x ∈ u, x ∈ D) (same : ∀ x, dominated s x ↔ dominated u x)
      (q : D) (hq : q ≠ P ∧ q ≠ R) :
      q ∈ restrictTypes D u du ∨ ∃ b ∈ restrictTypes D u du, ∃ rest : Multiset D,
        W b = W b + (W q + weight W rest) := by
    obtain ⟨b,hb,le⟩ := (same q.val).mp (old hq)
    rcases le.eq_or_lt with e|lt
    · exact Or.inl ((mem_restrict D u du q).mpr (e ▸ hb))
    · obtain ⟨rest,cut,low⟩ := extract q.val b lt
      have dr : ∀ z ∈ rest, z ∈ D := fun z hz => .inr (.inr ((same z).mpr ⟨b,hb,low z hz⟩))
      exact Or.inr ⟨⟨b,du b hb⟩,(mem_restrict D u du _).mpr hb,restrictTypes D rest dr,
        by simpa only [W,restrict_weight] using cut⟩
  rw [← restrict_weight w D s ds,← restrict_weight w D t dt] at eb eg ⊢
  apply compare_box_unions W P R nPR (dim ∘ Subtype.val) F
    (fun q h => by simpa only [W,faceVal q h] using cut _ (reg h))
    (fun q h => by simpa only [Function.comp_apply,faceVal q h] using lower _ (reg h))
    bounded geometric bp br gp gr _ _ _ eb eg
  rintro u (h|h)
  · subst u; exact available s ds (fun _ => Iff.rfl)
  · obtain rfl : u = restrictTypes D t dt := h
    exact available t dt dom

end GeneralizedEuler.Section4.BoxMultiplicity
