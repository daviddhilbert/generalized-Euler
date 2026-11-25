module

public import Section3.ExponentialObstruction
public import Section3.AtomicIntervals
import all Section3.AtomicIntervals
public import Section2.ContinuousDefinitions

public section

namespace GeneralizedEuler.Section3

open Set FirstOrder FirstOrder.Language GeneralizedEuler.Section2

variable {k H : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] {L : Language} [L.Structure k]

omit [Field k] [IsStrictOrderedRing k] in
private theorem residue_first_nonempty (hom : IsOMinimal (K := k) L) {S : Set k}
    (defS : (univ : Set k).Definable₁ L S) (hne : S.Nonempty) : (firstComponent S).Nonempty := by
  classical
  obtain ⟨cells,shape,cov⟩ := hom S defS
  let I := {c : cells // c.val.Nonempty}
  have cover (x : k) : x ∈ S ↔ ∃ i : I, x ∈ i.val.val := by
    rw [cov]
    exact ⟨fun h => by obtain ⟨c,hc,hx⟩ := mem_iUnion₂.mp h; exact ⟨⟨⟨c,hc⟩,x,hx⟩,hx⟩,
      fun ⟨i,h⟩ => mem_iUnion₂.mpr ⟨i.val.val,i.val.property,h⟩⟩
  obtain ⟨x,hx⟩ := hne
  obtain ⟨i,_⟩ := (cover x).mp hx
  let : Nonempty I := ⟨i⟩
  let rep (j : I) := j.property.choose
  obtain ⟨m,hm⟩ := Finite.exists_min rep
  refine ⟨rep m,(cover _).mpr ⟨m,m.property.choose_spec⟩,?_⟩
  intro y hy z hyz hzm
  obtain ⟨j,hj⟩ := (cover y).mp hy
  have conv : j.val.val.OrdConnected := by
    rcases shape j.val.val j.val.property with he | ⟨_,he⟩ | ⟨_,he⟩ | ⟨_,he⟩ | ⟨_,_,he⟩ <;> rw [he] <;> infer_instance
  exact (cover _).mpr ⟨j,conv.out hj j.property.choose_spec ⟨hyz,hzm.trans (hm j)⟩⟩

private def residueOrderIso (e : k ≃+* k) (mono : StrictMono e) : k ≃o k :=
  ⟨e.toEquiv,mono.le_iff_le⟩

/-- Canonical unary choice in an o-minimal ordered field, in the form
needed with imaginary parameters. Every ordered field automorphism
preserving the set fixes the same chosen point. The endpoints of the
first convex component suffice, including on an unbounded component. -/
theorem invariant_residue_point (hom : IsOMinimal (K := k) L) {F : OrderedFieldTerms L}
    (hF : InterpretsOrderedFieldTerms (A := k) F) {S : Set k} (defS : (univ : Set k).Definable₁ L S)
    (hne : S.Nonempty) (e : H → k ≃+* k) (mono : ∀ i, StrictMono (e i))
    (stable : ∀ i x, x ∈ S ↔ e i x ∈ S) : ∃ x ∈ S, ∀ i, e i x = x := by
  let C := firstComponent S
  have dne := residue_first_nonempty hom defS hne
  have defC := definable_firstComponent F.le hF.le defS
  have cv : C.OrdConnected := by
    refine ⟨fun {x} hx {y} hy z hz => ⟨hy.2 x hx.1 z hz.1 hz.2,?_⟩⟩
    exact fun u hu v huv hvz => hy.2 u hu v huv (hvz.trans hz.2)
  have stableC (i : H) (x : k) : x ∈ C ↔ e i x ∈ C := by
    constructor
    · intro hx
      refine ⟨(stable i x).mp hx.1,?_⟩
      intro y hy z hyz hzx
      obtain ⟨y,rfl⟩ := (e i).surjective y
      obtain ⟨z,rfl⟩ := (e i).surjective z
      exact (stable i z).mp (hx.2 y ((stable i y).mpr hy) z ((mono i).le_iff_le.mp hyz) ((mono i).le_iff_le.mp hzx))
    · intro hx
      exact ⟨(stable i x).mpr hx.1,fun y hy z hyz hzx => (stable i z).mpr
        (hx.2 _ ((stable i y).mp hy) _ ((mono i).monotone hyz) ((mono i).monotone hzx))⟩
  have im (i : H) : (residueOrderIso (e i) (mono i)) '' C = C := by
    ext x
    obtain ⟨y,rfl⟩ := (e i).surjective x
    exact ((residueOrderIso (e i) (mono i)).toEquiv.injective.mem_set_image).trans (stableC i y)
  have fixedLo {a : k} (h : IsGLB C a) (i : H) : e i a = a := by
    have h' := (residueOrderIso (e i) (mono i)).isGLB_image'.mpr h
    rw [im i] at h'
    exact h'.unique h
  have fixedHi {b : k} (h : IsLUB C b) (i : H) : e i b = b := by
    have h' := (residueOrderIso (e i) (mono i)).isLUB_image'.mpr h
    rw [im i] at h'
    exact h'.unique h
  have inside {q : k} (lo : ∃ u ∈ C, u ≤ q) (hi : ∃ v ∈ C, q ≤ v) : q ∈ S := by
    obtain ⟨u,hu,hl⟩ := lo
    obtain ⟨v,hv,hh⟩ := hi
    exact (cv.out hu hv ⟨hl,hh⟩).1
  have low {a q : k} (h : IsGLB C a) (lt : a < q) : ∃ u ∈ C, u ≤ q := by
    by_contra! fail
    exact lt.not_ge (h.2 (fun u hu => (fail u hu).le))
  have high {b q : k} (h : IsLUB C b) (lt : q < b) : ∃ u ∈ C, q ≤ u := by
    by_contra! fail
    exact lt.not_ge (h.2 (fun u hu => (fail u hu).le))
  by_cases lower : BddBelow C
  · obtain ⟨a,ha⟩ := hom.exists_isGLB defC dne lower
    by_cases upper : BddAbove C
    · obtain ⟨b,hb⟩ := exists_lub_of_ominimal hom defC dne upper
      obtain ⟨x,hx⟩ := dne
      have ax := ha.1 hx
      have xb := hb.1 hx
      rcases (ax.trans xb).eq_or_lt with same | lt
      · have he : a = x := le_antisymm ax (same.symm ▸ xb)
        exact ⟨a,he.symm ▸ hx.1,fixedLo ha⟩
      · exact ⟨(a+b)/2,inside (low ha (by linarith)) (high hb (by linarith)),
          fun i => by simp [fixedLo ha i,fixedHi hb i,show e i (2 : k) = 2 by rw [show (2 : k) = 1+1 by norm_num,map_add,map_one] ]⟩
    · obtain ⟨z,hz,hz'⟩ := not_bddAbove_iff.mp upper (a+1)
      exact ⟨a+1,inside (low ha (by linarith)) ⟨z,hz,hz'.le⟩,fun i => by simp [fixedLo ha i]⟩
  · by_cases upper : BddAbove C
    · obtain ⟨b,hb⟩ := exists_lub_of_ominimal hom defC dne upper
      obtain ⟨z,hz,hz'⟩ := not_bddBelow_iff.mp lower (b-1)
      exact ⟨b-1,inside ⟨z,hz,hz'.le⟩ (high hb (by linarith)),fun i => by simp [fixedHi hb i]⟩
    · obtain ⟨z,hz,hz'⟩ := not_bddBelow_iff.mp lower 0
      obtain ⟨w,hw,hw'⟩ := not_bddAbove_iff.mp upper 0
      exact ⟨0,inside ⟨z,hz,hz'.le⟩ ⟨w,hw,hw'.le⟩,fun i => map_zero (e i)⟩

/-- Coordinate projections and fibers extend invariant choice to every
finite tuple of residue parameters for a formula scheme. -/
theorem invariant_residue_tuple (hom : IsOMinimal (K := k) L) {F : OrderedFieldTerms L}
    (hF : InterpretsOrderedFieldTerms (A := k) F) (e : H → k ≃+* k) (mono : ∀ i, StrictMono (e i))
    {n : ℕ} {S : Set (Fin n → k)} (hd : (univ : Set k).Definable L S) (hne : S.Nonempty)
    (stable : ∀ i p, p ∈ S ↔ (e i ∘ p) ∈ S) : ∃ p ∈ S, ∀ i j, e i (p j) = p j := by
  induction n with
  | zero => exact ⟨hne.choose,hne.choose_spec,fun _ j => j.elim0⟩
  | succ n ih =>
    let A := (fun v : Fin (n+1) → k => v 0) '' S
    have defA : (univ : Set k).Definable₁ L A := by
      change (univ : Set k).Definable L {w : Fin 1 → k | w 0 ∈ A}
      convert hd.image_comp (fun _ : Fin 1 => (0 : Fin (n+1))) using 1
      ext w
      exact ⟨fun ⟨v,hv,he⟩ => ⟨v,hv,funext fun j => (Fin.fin_one_eq_zero j).symm ▸ he⟩,
        fun ⟨v,hv,he⟩ => ⟨v,hv,congrFun he 0⟩⟩
    have invA (i : H) (z : k) : z ∈ A ↔ e i z ∈ A := by
      constructor
      · rintro ⟨v,hv,rfl⟩; exact ⟨e i ∘ v,(stable i v).mp hv,rfl⟩
      · rintro ⟨v,hv,he⟩
        let w := (e i).symm ∘ v
        have hw : e i ∘ w = v := funext fun j => (e i).apply_symm_apply _
        exact ⟨w,(stable i w).mpr (hw.symm ▸ hv),(e i).injective ((congrFun hw 0).trans he)⟩
    obtain ⟨z,hz,fixz⟩ := invariant_residue_point hom hF defA (hne.image _) e mono invA
    let B := {v : Fin n → k | Fin.cons z v ∈ S}
    have defB : (univ : Set k).Definable L B := by
      apply hd.preimage_map (F := fun v => Fin.cons z v)
      intro j
      cases j using Fin.cases with
      | zero => exact L.definableFun_const _ (mem_univ z)
      | succ j => exact DefinableFun.proj L
    obtain ⟨v,hv,hzv⟩ := hz
    have hneB : B.Nonempty := ⟨Fin.tail v,by change Fin.cons z (Fin.tail v) ∈ S; rw [←hzv,Fin.cons_self_tail]; exact hv⟩
    have commute (i : H) (p : Fin n → k) : e i ∘ Fin.cons z p = Fin.cons z (e i ∘ p) := by
      funext j
      cases j using Fin.cases with
      | zero => exact fixz i
      | succ j => rfl
    obtain ⟨p,hp,hfix⟩ := ih defB hneB (fun i p => by
      change Fin.cons z p ∈ S ↔ Fin.cons z (e i ∘ p) ∈ S
      rw [←commute]; exact stable i _)
    refine ⟨Fin.cons z p,hp,fun i j => ?_⟩
    cases j using Fin.cases with
    | zero => exact fixz i
    | succ j => exact hfix i j

end GeneralizedEuler.Section3
