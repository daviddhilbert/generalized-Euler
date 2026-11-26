module

public import Section4.RVTaggedEquivalence
public import Section4.LocalRVMeasure
import all Section4.RVTaggedEquivalence
import all Section4.LocalRVMeasure

/-! Compare sums over a tagged definable bijection by cutting each side
according to the opposite tag. The input and output arities can differ. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.RVFamily
open FirstOrder GeneralizedEuler.Section2
set_option backward.isDefEq.respectTransparency false
variable {L : Language} {F : Type*} {Z : TCsort → Type*} {M : SortedStructure L F Z} {S : SortedSubstructure M}
  (A B : RVFamily M S) (f : A.Points ≃ B.Points)
  (graph : ∀ i j, isRVSet M S (graphPiece A B f i j))

def branch (i : A.Tag) (j : B.Tag) (x : A.Coord i → Z .rv) (y : B.Coord j → Z .rv) : Prop :=
  Sum.elim x y ∈ graphPiece A B f i j

private theorem branch_iff (i j) (x : A.piece i) (y : B.piece j) :
    branch A B f i j x.val y.val ↔ f ⟨i,x⟩ = ⟨j,y⟩ := by
  constructor
  · rintro ⟨a,b,ha,hb,h⟩
    have l : a=x := Subtype.ext ha
    have r : b=y := Subtype.ext hb
    exact l ▸ r ▸ h
  · exact fun h => ⟨x,y,rfl,rfl,h⟩

private def domain (i : A.Tag) (j : B.Tag) : Set (A.Coord i → Z .rv) := {x | ∃ y, branch A B f i j x y}
private def range (i : A.Tag) (j : B.Tag) : Set (B.Coord j → Z .rv) := {y | ∃ x, branch A B f i j x y}

private theorem matched (i j) {x y} (h : branch A B f i j x y) :
    ∃ (hx : x ∈ A.piece i) (hy : y ∈ B.piece j), f ⟨i,x,hx⟩ = ⟨j,y,hy⟩ := by
  obtain ⟨a,b,l,r,e⟩ := h
  change a.val = x at l; change b.val = y at r
  exact ⟨l ▸ a.property,r ▸ b.property,by obtain rfl : a.val=x := l; obtain rfl : b.val=y := r; exact e⟩

include graph in
private theorem branch_equivalent (i j) :
    RVDefinablyEquivalent M S.carrier (domain A B f i j) (range A B f i j) := by
  let R := branch A B f i j
  have single {x y z} (a : R x y) (b : R x z) : y=z := by
    obtain ⟨_,_,h⟩ := matched A B f i j a
    obtain ⟨_,_,h'⟩ := matched A B f i j b
    exact congrArg Subtype.val (Sigma.mk.inj_iff.mp (h.symm.trans h')).2.eq
  have inj {x z y} (a : R x y) (b : R z y) : x=z := by
    obtain ⟨_,_,h⟩ := matched A B f i j a
    obtain ⟨_,_,h'⟩ := matched A B f i j b
    exact congrArg Subtype.val (Sigma.mk.inj_iff.mp (f.injective (h.trans h'.symm))).2.eq
  let e := matchingGraphEquiv R (fun h h' => single h h') (fun h h' => inj h h')
  have law (a) (b) := matchingGraphEquiv_iff R (fun h h' => single h h') (fun h h' => inj h h') a b
  refine ⟨e,?_⟩
  let G := {p : A.Coord i ⊕ B.Coord j → Z .rv | ∃ a : domain A B f i j, a.val = p ∘ Sum.inl ∧ (e a).val = p ∘ Sum.inr}
  change isRVSet M S G
  refine (show G = graphPiece A B f i j from ?_).symm ▸ graph i j
  apply Set.ext; intro w
  have rebuild : Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := funext (Sum.rec (fun _ => rfl) (fun _ => rfl))
  constructor
  · rintro ⟨a,l,h⟩
    have rel := (law a _).mp h
    change Sum.elim a.val (w ∘ Sum.inr) ∈ _ at rel
    rwa [l,rebuild] at rel
  · intro h
    have r : R (w ∘ Sum.inl) (w ∘ Sum.inr) := (congrArg (· ∈ graphPiece A B f i j) rebuild).mpr h
    exact ⟨⟨_,_,r⟩,rfl,(law _ _).mpr r⟩

variable [Fintype A.Tag] [Fintype B.Tag] {P : Z .rv → Prop} {k : ℕ} {T : Type*} [AddCommMonoid T]
  (μ : LocalRVMeasure M S P k T)
  (c : (i : A.Tag) → LocalRVMeasure.Cell M S P k (A.Coord i))
  (d : (j : B.Tag) → LocalRVMeasure.Cell M S P k (B.Coord j))

include graph in
theorem sum_cells_eq (ca : ∀ i, (c i).carrier = A.piece i) (cb : ∀ j, (d j).carrier = B.piece j) :
    ∑ i, μ.weight (c i).model (c i).good = ∑ j, μ.weight (d j).model (d j).good := by
  have ds i j : isRVSet M S (domain A B f i j) := isRVSet_project (graph i j)
  have rs i j : isRVSet M S (range A B f i j) := by
    let R := {w : B.Coord j ⊕ A.Coord i → Z .rv | w ∘ Sum.swap ∈ graphPiece A B f i j}
    have h := isRVSet_project (D := R) (isRVSet_precomp Sum.swap (graph i j))
    refine (show range A B f i j = {y | ∃ x, Sum.elim y x ∈ R} from ?_).symm ▸ h
    apply Set.ext; intro y
    apply exists_congr; intro x
    exact (congrArg (· ∈ graphPiece A B f i j) (show Sum.elim x y = Sum.elim y x ∘ Sum.swap from funext (Sum.rec (fun _ => rfl) (fun _ => rfl)))).to_iff
  have row i : Pairwise (fun j l => Disjoint (domain A B f i j) (domain A B f i l)) := by
    intro j l ne; apply Set.disjoint_left.mpr; rintro x ⟨y,a⟩ ⟨z,b⟩
    obtain ⟨_,_,h⟩ := matched A B f i j a
    obtain ⟨_,_,h'⟩ := matched A B f i l b
    exact ne (congrArg Sigma.fst (h.symm.trans h'))
  have col j : Pairwise (fun i l => Disjoint (range A B f i j) (range A B f l j)) := by
    intro i l ne; apply Set.disjoint_left.mpr; rintro y ⟨x,a⟩ ⟨z,b⟩
    obtain ⟨_,_,h⟩ := matched A B f i j a
    obtain ⟨_,_,h'⟩ := matched A B f l j b
    exact ne (congrArg Sigma.fst (f.injective (h.trans h'.symm)))
  have rc i : (⋃ j, domain A B f i j) = (c i).carrier := by
    rw [ca]; ext x; rw [Set.mem_iUnion]; constructor
    · rintro ⟨j,y,h⟩; exact (matched A B f i j h).choose
    · intro hx
      let y := f ⟨i,x,hx⟩
      exact ⟨y.1,y.2.val,(branch_iff A B f i y.1 ⟨x,hx⟩ y.2).mpr rfl⟩
  have cc j : (⋃ i, range A B f i j) = (d j).carrier := by
    rw [cb]; ext y; rw [Set.mem_iUnion]; constructor
    · rintro ⟨i,x,h⟩; exact (matched A B f i j h).choose_spec.choose
    · intro hy
      let x := f.symm ⟨j,y,hy⟩
      exact ⟨x.1,x.2.val,(branch_iff A B f x.1 j x.2 ⟨y,hy⟩).mpr (f.apply_symm_apply _)⟩
  choose a ha wa using fun i => μ.cut_cell (c i) (domain A B f i) (ds i) (row i) (rc i)
  choose b hb wb using fun j => μ.cut_cell (d j) (fun i => range A B f i j) (fun i => rs i j) (col j) (cc j)
  have eq i j : μ.weight (a i j).model (a i j).good = μ.weight (b j i).model (b j i).good := by
    apply μ.iso
    have l := (a i j).identifies.symm
    have r := (b j i).identifies
    rw [ha] at l; rw [hb] at r
    exact (l.trans (branch_equivalent A B f graph i j)).trans r
  simp_rw [wa,wb,eq]; exact Finset.sum_comm

end GeneralizedEuler.Section4.RVFamily
