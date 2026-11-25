module

public import Section3.DiscGraphImages
import all Section3.DiscGraphImages
import all Section3.PolydiscImages
import all Section3.DiscAtomicSlices

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2 FirstOrder

variable {K I : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : Language} [L.Structure K] (O : ValuationSubring K) (hO : IsOrderConvex O)
    {C : Set (I → K)} {P : Set K} {F : FieldTerms L}

private theorem image_of_atomic_unary [DenselyOrdered O.ValueGroup]
    (hF : InterpretsFieldTerms (K := K) F) (center : K) (r : O.ValueGroup)
    (f : K → K) (A : Set K) (disc : A = openDisc O center r)
    (atom : AtomicOver (OverRepresentativeClass (L := L) P C) {u : Unit → K | u () ∈ A})
    (graph : OverRepresentativeClass (L := L) P C (unaryFieldGraph A f))
    (taxonomy : ∀ B, AtomicOver (UnaryOverClass (L := L) P C) B → IsAtomicShape O B)
    (pieces : ∃ (m : ℕ) (B : Fin m → Set K), A ⊆ ⋃ i, B i ∧
      ∀ i, UnaryOverClass (L := L) P C (B i) ∧ MonotonePiece f (B i))
    (stability : ∀ g : K → K, OverRepresentativeClass (L := L) P C (unaryFieldGraph univ g) →
      ∀ c u : K, EventuallyConstantValue O hO (fun z => g (c+u*z.val)-center)) :
    IsPointOrOpen O (f '' A) := by
  have im := atomic_image_with_representatives atom (fun u => f (u ())) graph
  have eqIm : (fun u : Unit → K => f (u ())) '' {u | u () ∈ A} = f '' A := by
    ext v
    exact ⟨fun ⟨u,hu,he⟩ => ⟨u (),hu,he⟩,fun ⟨x,hx,he⟩ => ⟨fun _ => x,hx,he⟩⟩
  rw [eqIm] at im
  obtain ⟨m,B,cover,mono⟩ := pieces
  obtain ⟨a,ha⟩ := atom.2.nonempty
  obtain ⟨j,hj⟩ := mem_iUnion.mp (cover ha)
  have sub : A ⊆ B j := fun x hx =>
    (atom.2.uniform _ (mono j).1 a ha (fun _ => x) hx).mp hj
  have monotone := (mono j).2.restrict sub
  have eliminate (inj : InjOn f A) (mon : MonotoneOn f A ∨ AntitoneOn f A) :
      IsPointOrOpen O (f '' A) := by
    obtain ⟨g,inv,dg⟩ := definable_total_inverse F hF graph inj
    subst A
    exact unary_atomic_disc_image O hO center r f g inv mon (taxonomy _ im) (stability g dg)
  cases monotone with
  | const eq =>
    left
    refine ⟨f (a ()),?_⟩
    ext z
    exact ⟨fun ⟨x,hx,he⟩ => he ▸ eq x hx (a ()) ha,
      fun hz => ⟨a (),ha,(mem_singleton_iff.mp hz).symm⟩⟩
  | increasing inc => exact eliminate inc.injOn (Or.inl inc.monotoneOn)
  | decreasing dec => exact eliminate dec.injOn (Or.inr dec.antitoneOn)

/-- Lemma 3.13 using exactly the unary taxonomy (3.11), definable
monotonicity (3.4) and the cofinal-value assertion (3.2) for translated
inverse branches. Inputs are stated for all parameter extensions used by
the slices. The original polydisc and graph may use named disc codes. -/
theorem atomic_polydisc_image [Finite I] [DenselyOrdered O.ValueGroup]
    (hF : InterpretsFieldTerms (K := K) F) (hc : C.Nonempty)
    (eqn : L.Formula (I ⊕ I)) (he : ∀ c ∈ C, ∀ d, eqn.Realize (Sum.elim c d) ↔ d ∈ C)
    (taxonomy : ∀ (Q : Set K) B, AtomicOver (UnaryOverClass (L := L) Q C) B → IsAtomicShape O B)
    (monotonicity : ∀ (Q : Set K) A (g : K → K), OverRepresentativeClass (L := L) Q C (unaryFieldGraph A g) →
      ∃ (m : ℕ) (B : Fin m → Set K), A ⊆ ⋃ i, B i ∧
        ∀ i, UnaryOverClass (L := L) Q C (B i) ∧ MonotonePiece g (B i))
    (stability : ∀ (Q : Set K) g, OverRepresentativeClass (L := L) Q C (unaryFieldGraph univ g) →
      ∀ a c u : K, EventuallyConstantValue O hO (fun z => g (c+u*z.val)-a))
    {n : ℕ} (center : Fin n → K) (r : Fin n → O.ValueGroup) (f : (Fin n → K) → K)
    (atom : AtomicOver (OverRepresentativeClass (L := L) P C) {x | ∀ i, x i ∈ openDisc O (center i) (r i)})
    (graph : OverRepresentativeClass (L := L) P C (FieldGraphOn {x | ∀ i, x i ∈ openDisc O (center i) (r i)} f)) :
    let B := f '' {x | ∀ i, x i ∈ openDisc O (center i) (r i)}
    AtomicOver (UnaryOverClass (L := L) P C) B ∧ IsPointOrOpen O B ∧ ∃ t, ∀ y ∈ B, rv O y = t := by
  let D := fun i => openDisc O (center i) (r i)
  let B := f '' {x | ∀ i, x i ∈ D i}
  have im : AtomicOver (UnaryOverClass (L := L) P C) B := atomic_image_with_representatives atom f graph
  have shape : IsPointOrOpen O B := by
    apply polydisc_image_of_unary_slices O hO f D _ (taxonomy P B im)
    intro i x hx
    cases n with
    | zero => exact i.elim0
    | succ d =>
      let Q := P ∪ range (i.removeNth x)
      let g (v : K) := f (Function.update x i v)
      have atSlice := atomic_coordinate_with_representatives P C hc eqn he D atom i x hx
      have graphSlice := coordinate_graph_with_representatives D f graph i x hx
      exact image_of_atomic_unary O hO hF (center i) (r i) g (D i) rfl atSlice graphSlice
        (taxonomy Q) (monotonicity Q _ g graphSlice) (fun k hk => stability Q k hk (center i))
  exact ⟨im,shape,rv_constant_of_atomic_point_or_open O im.2 (unary_zero_over_class F hF) shape⟩

end GeneralizedEuler.Section3
