module

public import Section3.AffineSlopes
public import Section3.FieldBranches
public import Section3.DiscMapPartitions
public import Section3.DerivativeFormula
public import Section3.DiscGraphImages
import all Section3.DiscAtomicSlices
import all Section3.DiscGraphImages

public section

namespace GeneralizedEuler.Section3

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set

variable {K I : Type*} {L : Language} [L.Structure K] {P : Set K} {C : Set (I → K)}

theorem overClass_of_definable {V : Type*} {A : Set (V → K)} (h : P.Definable L A) :
    OverRepresentativeClass (L := L) P C A := by
  obtain ⟨φ,hφ⟩ := definable_iff_exists_formula_sum.mp h
  refine ⟨φ.relabel (Sum.map id Sum.inl),fun x c _ => ?_⟩
  rw [Formula.realize_relabel,hφ]
  have he : Sum.elim (Subtype.val : P → K) (Sum.elim x c) ∘ Sum.map id Sum.inl =
      Sum.elim Subtype.val x := by funext j; cases j <;> rfl
  rw [he]
  rfl

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (O : ValuationSubring K) [DenselyOrdered O.ValueGroup]

/-- Lemma 3.36. Select the pure field branch on the atom, define the
locus of differentiation by the ordered-field formula and propagate
differentiability from one point. Apply the RV constancy assertion of
3.13 to the graph of the uniquely determined derivative. The only
calculus inputs are generic differentiability and the mean value theorem
for the pure branches. -/
theorem atomic_open_disc_affine {F : OrderedFieldTerms L} (hF : InterpretsOrderedFieldTerms (A := K) F)
    {a b : K} {r s : O.ValueGroup} (hr : r ≠ 0)
    (f : K → K) (bij : BijOn f (openDisc O a r) (openDisc O b s))
    (atom : AtomicOver (UnaryOverClass (L := L) P C) (openDisc O a r))
    {J : Type*} (branch : J → K → K)
    (terms : ∀ j, P.DefinableFun L (fun v : Unit → K => branch j (v ())))
    (agreement : ∀ j, UnaryOverClass (L := L) P C {x | branch j x = f x})
    (cover : ∀ x ∈ openDisc O a r, ∃ j, branch j x = f x)
    (differentiate : ∀ j, ∃ x ∈ openDisc O a r, ∃ m, HasOrderDerivativeAt (branch j) x m)
    (meanValue : ∀ j, (∀ x ∈ openDisc O a r, ∃ m, HasOrderDerivativeAt (branch j) x m) →
      ∀ x ∈ openDisc O a r, ∀ y ∈ openDisc O a r, x ≠ y → ∃ z ∈ openDisc O a r,
        ∃ m, HasOrderDerivativeAt (branch j) z m ∧ branch j x - branch j y = m*(x-y))
    (rvImage : ∀ d : K → K, OverRepresentativeClass (L := L) P C (unaryFieldGraph (openDisc O a r) d) →
      ∃ t, ∀ y ∈ d '' openDisc O a r, rv O y = t) :
    ∃ t : RV O, RVAffineOn O (openDisc O a r) f t ∧
      ValAffineOn O (openDisc O a r) f (unsignedValueUnit O t) ∧
      s = (unsignedValueUnit O t : O.ValueGroup)*r := by
  classical
  let A := openDisc O a r
  obtain ⟨j,hj⟩ := single_field_branch_of_atomic_cover atom.2 f branch agreement cover
  let g := branch j
  let D := {w : Unit ⊕ Unit → K | HasOrderDerivativeAt g (w (.inl ())) (w (.inr ()))}
  have hd : P.Definable L D := by
    have h := definable_order_derivative_family F hF (I := Empty) (fun _ x => g x)
      ((terms j).comp (g := fun v : Empty ⊕ Unit → K => v ∘ Sum.inr) (fun _ => DefinableFun.proj L))
    let rename : Empty ⊕ Fin 2 → Unit ⊕ Unit := Sum.elim Empty.elim (Fin.cases (.inl ()) (fun _ => .inr ()))
    exact h.preimage_map (F := fun w => w ∘ rename) (fun _ => DefinableFun.proj L)
  have graph := overClass_of_definable (C := C) hd
  let good := {x : K | ∃ m, HasOrderDerivativeAt g x m}
  have dg : UnaryOverClass (L := L) P C good := by
    unfold UnaryOverClass
    convert graph.project using 1
    ext w
    change (∃ m, HasOrderDerivativeAt g (w ()) m) ↔ ∃ z : Unit → K, HasOrderDerivativeAt g (w ()) (z ())
    exact ⟨fun ⟨m,h⟩ => ⟨fun _ => m,h⟩,fun ⟨z,h⟩ => ⟨z (),h⟩⟩
  obtain ⟨x,hx,someD⟩ := differentiate j
  have allD (y : K) (hy : y ∈ A) : ∃ m, HasOrderDerivativeAt g y m :=
    (atom.2.uniform good dg x hx y hy).mp someD
  let d (z : K) := if h : z ∈ A then (allD z h).choose else 0
  have derivative (z : K) (hz : z ∈ A) : HasOrderDerivativeAt g z (d z) := by
    simpa [d,hz] using (allD z hz).choose_spec
  have gdef : OverRepresentativeClass (L := L) P C (unaryFieldGraph A d) := by
    have both := (OverRepresentativeClass.pullback atom.1 (Sum.inl : Unit → Unit ⊕ Unit)).inter graph
    convert both using 1
    ext w
    change (w (.inl ()) ∈ A ∧ w (.inr ()) = d (w (.inl ()))) ↔
      w (.inl ()) ∈ A ∧ HasOrderDerivativeAt g (w (.inl ())) (w (.inr ()))
    apply and_congr_right
    intro h
    exact ⟨fun e => e.symm ▸ derivative _ h,fun H => H.unique (derivative _ h)⟩
  obtain ⟨u,hu⟩ := rvImage d gdef
  obtain ⟨t,_,aff,shift⟩ := affine_openDisc_of_constant_derivative_rv O hr (openDisc_nontrivial O a hr)
    bij.injOn bij.image_eq (fun z h => hu _ (mem_image_of_mem d h)) (by
      intro x hx y hy hne
      obtain ⟨z,hz,m,hm,he⟩ := meanValue j allD x hx y hy hne
      exact ⟨z,hz,by rw [←hj hx,←hj hy,he,hm.unique (derivative z hz)]⟩)
  exact ⟨t,aff,aff.toValAffine O,shift⟩

end GeneralizedEuler.Section3
