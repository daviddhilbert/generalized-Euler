module

public import Section3.DiscAtomicSlices
import all Section3.DiscAtomicSlices
import all Section3.PolydiscImages

public section

namespace GeneralizedEuler.Section3

open FirstOrder FirstOrder.Language GeneralizedEuler.Section2 Set

variable {K V W I : Type*} {L : Language} [L.Structure K] {P : Set K} {C : Set (I → K)}

theorem OverRepresentativeClass.inter {A B : Set (V → K)}
    (hA : OverRepresentativeClass (L := L) P C A) (hB : OverRepresentativeClass (L := L) P C B) :
    OverRepresentativeClass (L := L) P C (A ∩ B) := by
  obtain ⟨φ,hφ⟩ := hA
  obtain ⟨ψ,hψ⟩ := hB
  exact ⟨φ ⊓ ψ,fun x c hc => ((hφ x c hc).and (hψ x c hc)).trans Formula.realize_inf.symm⟩

theorem OverRepresentativeClass.project {A : Set (V ⊕ W → K)} [Finite W]
    (hA : OverRepresentativeClass (L := L) P C A) :
    OverRepresentativeClass (L := L) P C {x | ∃ y, Sum.elim x y ∈ A} := by
  obtain ⟨φ,hφ⟩ := hA
  let rename : P ⊕ ((V ⊕ W) ⊕ I) → (P ⊕ (V ⊕ I)) ⊕ W
    | .inl p => .inl (.inl p)
    | .inr (.inl (.inl i)) => .inl (.inr (.inl i))
    | .inr (.inl (.inr j)) => .inr j
    | .inr (.inr i) => .inl (.inr (.inr i))
  refine ⟨Formula.iExs W (φ.relabel rename),fun x c hc => ?_⟩
  rw [Formula.realize_iExs]
  apply exists_congr
  intro y
  rw [Formula.realize_relabel]
  apply (hφ _ _ hc).trans
  apply Iff.of_eq
  congr 1
  funext i
  rcases i with p | ((j|j)|i) <;> rfl

def UnaryOverClass (P : Set K) (C : Set (I → K)) (U : Set K) : Prop :=
  OverRepresentativeClass (L := L) P C {v : Unit → K | v () ∈ U}

def FieldGraphOn (A : Set (V → K)) (f : (V → K) → K) : Set (V ⊕ Unit → K) :=
  {v | v ∘ Sum.inl ∈ A ∧ v (.inr ()) = f (v ∘ Sum.inl)}

/-- Atomic images for fixed disc imaginaries, including the definability
of the image and of each of the tests pulled back along a partial graph. -/
theorem atomic_image_with_representatives [Finite V] {A : Set (V → K)}
    (atom : AtomicOver (OverRepresentativeClass (L := L) P C) A) (f : (V → K) → K)
    (graph : OverRepresentativeClass (L := L) P C (FieldGraphOn A f)) :
    AtomicOver (UnaryOverClass (L := L) P C) (f '' A) := by
  let swap : V ⊕ Unit → Unit ⊕ V := Sum.elim Sum.inr Sum.inl
  have imageDef := (graph.pullback swap).project
  refine ⟨?_,atom.2.nonempty.image f,?_⟩
  · apply show UnaryOverClass (L := L) P C (f '' A) from ?_
    unfold UnaryOverClass
    convert imageDef using 1
    ext v
    change (∃ x ∈ A, f x = v ()) ↔ (∃ x : V → K, x ∈ A ∧ v () = f x)
    exact exists_congr (fun _ => and_congr_right (fun _ => eq_comm))
  rintro B hB _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  have dB : OverRepresentativeClass (L := L) P C {w : V ⊕ Unit → K | w (.inr ()) ∈ B} :=
    OverRepresentativeClass.pullback hB Sum.inr
  have pre := (graph.inter dB).project
  have mem (a : V → K) (ha : a ∈ A) :
      (∃ u : Unit → K, Sum.elim a u ∈ FieldGraphOn A f ∩ {w | w (.inr ()) ∈ B}) ↔ f a ∈ B :=
    ⟨fun ⟨_,⟨_,he⟩,hm⟩ => he ▸ hm,fun hm => ⟨fun _ => f a,⟨ha,rfl⟩,hm⟩⟩
  exact (mem x hx).symm.trans ((atom.2.uniform _ pre x hx y hy).trans (mem y hy))

theorem unary_zero_over_class [Field K] (F : FieldTerms L) (hF : InterpretsFieldTerms (K := K) F) :
    UnaryOverClass (L := L) P C {0} := by
  let z : L.Term (P ⊕ (Unit ⊕ I)) := F.zero.relabel Empty.elim
  refine ⟨(Term.var (.inr (.inl ()))).equal z,fun x c _ => ?_⟩
  simp only [Term.realize_relabel,Formula.realize_equal,Term.realize_var,Sum.elim_inr,Sum.elim_inl,z]
  have he : (Sum.elim (Subtype.val : P → K) (Sum.elim x c)) ∘ Empty.elim = Empty.elim := Subsingleton.elim _ _
  rw [he,hF.zero]
  rfl

theorem OverRepresentativeClass.compl {A : Set (V → K)}
    (hA : OverRepresentativeClass (L := L) P C A) : OverRepresentativeClass (L := L) P C Aᶜ := by
  obtain ⟨φ,hφ⟩ := hA
  exact ⟨φ.not,fun x c hc => (not_congr (hφ x c hc)).trans Formula.realize_not.symm⟩

theorem OverRepresentativeClass.union {A B : Set (V → K)}
    (hA : OverRepresentativeClass (L := L) P C A) (hB : OverRepresentativeClass (L := L) P C B) :
    OverRepresentativeClass (L := L) P C (A ∪ B) := by
  obtain ⟨φ,hφ⟩ := hA
  obtain ⟨ψ,hψ⟩ := hB
  exact ⟨φ ⊔ ψ,fun x c hc => ((hφ x c hc).or (hψ x c hc)).trans Formula.realize_sup.symm⟩

theorem OverRepresentativeClass.specialize {A : Set (V → K)} {Q : Set K}
    (hA : OverRepresentativeClass (L := L) P C A) (hq : P ⊆ Q) (j : V → Q ⊕ W) :
    OverRepresentativeClass (L := L) Q C {u | Sum.elim Subtype.val u ∘ j ∈ A} := by
  obtain ⟨φ,hφ⟩ := hA
  let rename : P ⊕ (V ⊕ I) → Q ⊕ (W ⊕ I)
    | .inl p => .inl ⟨p.val,hq p.property⟩
    | .inr (.inl i) => (j i).map id Sum.inl
    | .inr (.inr i) => .inr (.inr i)
  refine ⟨φ.relabel rename,fun u c hc => ?_⟩
  rw [Formula.realize_relabel]
  apply (hφ _ _ hc).trans
  apply Iff.of_eq
  congr 1
  funext z
  rcases z with p | i | i
  · rfl
  · change Sum.elim Subtype.val u (j i) = Sum.elim Subtype.val (Sum.elim u c) ((j i).map id Sum.inl)
    cases j i <;> rfl
  · rfl

/-- The graph obtained from a partial definable graph by fixing all but
one input coordinate. Its only additional field parameters are the other
coordinates, even when the original graph uses independent disc codes. -/
theorem coordinate_graph_with_representatives {n : ℕ} (D : Fin (n+1) → Set K)
    (f : (Fin (n+1) → K) → K) (graph : OverRepresentativeClass (L := L) P C
      (FieldGraphOn {u | ∀ i, u i ∈ D i} f)) (j : Fin (n+1)) (a : Fin (n+1) → K) (ha : ∀ i, a i ∈ D i) :
    OverRepresentativeClass (L := L) (P ∪ range (j.removeNth a)) C
      (FieldGraphOn {u : Unit → K | u () ∈ D j} (fun u => f (Function.update a j (u ())))) := by
  let Q := P ∪ range (j.removeNth a)
  let fix (i : Fin n) : Q ⊕ (Unit ⊕ Unit) := .inl ⟨a (j.succAbove i),Or.inr ⟨i,rfl⟩⟩
  let rename : Fin (n+1) ⊕ Unit → Q ⊕ (Unit ⊕ Unit) :=
    Sum.elim (j.succAboveCases (.inr (.inl ())) fix) (fun _ => .inr (.inr ()))
  convert graph.specialize (Q := Q) subset_union_left rename using 1
  ext u
  let v := Sum.elim Subtype.val u ∘ rename
  have actual : v ∘ Sum.inl = Function.update a j (u (.inl ())) := by
    funext i
    refine j.succAboveCases ?_ (fun k => ?_) i
    · simp [v,rename]
    · simp [v,rename,fix]
  change (u (.inl ()) ∈ D j ∧ u (.inr ()) = _) ↔ ((∀ k, (v ∘ Sum.inl) k ∈ D k) ∧ u (.inr ()) = f (v ∘ Sum.inl))
  rw [actual]
  apply and_congr_left
  intro _
  constructor
  · intro hj k
    by_cases he : k = j
    · subst k; simpa using hj
    · simpa [Function.update_of_ne he] using ha k
  · intro hall
    simpa using hall j

abbrev unaryFieldGraph (A : Set K) (f : K → K) :=
  FieldGraphOn {a : Unit → K | a () ∈ A} (fun a => f (a ()))

/-- A partial inverse has a definable total extension by zero. Swapping
the graph handles points in the image. The complement of the image
selects the added zero branch. -/
theorem definable_total_inverse [Field K] {A : Set K} {f : K → K}
    (F : FieldTerms L) (hF : InterpretsFieldTerms (K := K) F)
    (graph : OverRepresentativeClass (L := L) P C (unaryFieldGraph A f)) (inj : InjOn f A) :
    ∃ g : K → K, LeftInvOn g f A ∧ OverRepresentativeClass (L := L) P C (unaryFieldGraph univ g) := by
  classical
  let g (z : K) := if h : z ∈ f '' A then h.choose else 0
  have inv : LeftInvOn g f A := by
    intro x hx
    have hv : f x ∈ f '' A := ⟨x,hx,rfl⟩
    rw [show g (f x) = _ from dite_eq_left hv]
    exact inj hv.choose_spec.1 hx hv.choose_spec.2
  refine ⟨g,inv,?_⟩
  let swap := Sum.elim (Sum.inr : Unit → Unit ⊕ Unit) Sum.inl
  have swapped := graph.pullback swap
  have inImage : OverRepresentativeClass (L := L) P C {v : Unit → K | v () ∈ f '' A} := by
    convert swapped.project using 1
    ext v
    change (∃ x ∈ A, f x = v ()) ↔ (∃ u : Unit → K, u () ∈ A ∧ v () = f (u ()))
    exact ⟨fun ⟨x,hx,he⟩ => ⟨fun _ => x,hx,he.symm⟩,fun ⟨u,hx,he⟩ => ⟨u (),hx,he.symm⟩⟩
  have zero : OverRepresentativeClass (L := L) P C {v : Unit → K | v () = 0} := unary_zero_over_class F hF
  have fallback := (inImage.compl.pullback (W := Unit ⊕ Unit) Sum.inl).inter (zero.pullback Sum.inr)
  convert swapped.union fallback using 1
  ext v
  let x := v (.inl ())
  let y := v (.inr ())
  change (_ ∈ univ ∧ y = g x) ↔ (y ∈ A ∧ x = f y) ∨ (x ∉ f '' A ∧ y = 0)
  rw [and_iff_right (mem_univ _)]
  by_cases hx : x ∈ f '' A
  · obtain ⟨z,hz,hzx⟩ := hx
    rw [←hzx,inv hz]
    exact ⟨fun h => Or.inl ⟨h ▸ hz,congrArg f h.symm⟩,
      fun h => h.elim (fun ⟨hy,he⟩ => inj hy hz he.symm) (fun ⟨no,_⟩ => (no ⟨z,hz,rfl⟩).elim)⟩
  · rw [show g x = 0 from dite_eq_right hx]
    exact ⟨fun h => Or.inr ⟨hx,h⟩,fun h => h.elim (fun ⟨hy,he⟩ => (hx ⟨y,hy,he.symm⟩).elim) And.right⟩

variable [Field K] (O : ValuationSubring K)

/-- The final assertion of 3.13, including constant images at zero. -/
theorem rv_constant_of_atomic_point_or_open {D : Set (Set K)} {A : Set K}
    (atom : GeneratesType D A) (dz : {0} ∈ D) (shape : IsPointOrOpen O A) :
    ∃ t, ∀ x ∈ A, rv O x = t := by
  by_cases hz : 0 ∈ A
  · refine ⟨rv O 0,fun x hx => congrArg (rv O) ?_⟩
    exact (atom.uniform {0} dz 0 hz x hx).mp rfl
  rcases shape with ⟨c,rfl⟩ | ⟨c,r,hr,rfl⟩
  · exact ⟨rv O c,fun _ hx => congrArg (rv O) (mem_singleton_iff.mp hx)⟩
  · exact ⟨rv O c,fun _ hx => rv_constant_on_open_omitting_zero O hr hz hx⟩

/-- Corollary 3.14 over the polydisc code. Intersect a separating test
with the domain to get the required definable proper subset of it. -/
theorem proper_subset_of_nonconstant_rv {A : Set (V → K)}
    (defA : OverRepresentativeClass (L := L) P C A) (f : (V → K) → K)
    (nonconstant : ∃ x ∈ A, ∃ y ∈ A, rv O (f x) ≠ rv O (f y))
    (image : AtomicOver (OverRepresentativeClass (L := L) P C) A →
      ∃ t, ∀ x ∈ A, rv O (f x) = t) :
    ∃ B, OverRepresentativeClass (L := L) P C B ∧ B.Nonempty ∧ B ⊂ A := by
  classical
  obtain ⟨x,hx,y,hy,hne⟩ := nonconstant
  by_contra no
  have uniform : AtomicOver (OverRepresentativeClass (L := L) P C) A := by
    refine ⟨defA,⟨x,hx⟩,?_⟩
    intro B hB a ha b hb
    have same (a b : V → K) (ha : a ∈ A) (hb : b ∈ A) (hm : a ∈ B) : b ∈ B := by
      by_contra hn
      exact no ⟨A ∩ B,defA.inter hB,⟨a,ha,hm⟩,inter_subset_left,fun h => hn (h hb).2⟩
    exact ⟨same a b ha hb,same b a hb ha⟩
  obtain ⟨t,ht⟩ := image uniform
  exact hne ((ht x hx).trans (ht y hy).symm)

end GeneralizedEuler.Section3
