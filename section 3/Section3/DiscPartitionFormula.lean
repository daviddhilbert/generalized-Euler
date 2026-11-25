module

public import Section3.ObjectPartitions
public import Section2.RecoveredValuedField
public import Section2.ValuedFieldFormulas
import all Section2.SortedQuantifierBlock
import all Section3.BoundaryBranches
import all Section2.SortedSyntax

public section

namespace GeneralizedEuler.Section3.DiscPartition

open GeneralizedEuler.Section2 FirstOrder FirstOrder.Language Set
universe u
variable {L : Language.{u,u}} {E : Type u} {V W X : TCsort → Type u} {n m : ℕ}

abbrev FBlock (V : TCsort → Type u) (k : ℕ) := AddSortedBlock V .vf k
abbrev fresh {V : TCsort → Type u} {k : ℕ} (j : Fin k) : FBlock V k .vf := .inr ⟨j,⟨rfl⟩⟩
abbrev FV (k : ℕ) := FBlock (fun _ => PEmpty.{u+1}) k

private def instantiate (p : ∀ s, V s → W s) (x : Fin n → W .vf) (φ : SortedFormula L E (FBlock V n)) :=
  φ.relabel (fun s z => match z with
    | .inl j => p s j
    | .inr ⟨j,⟨h⟩⟩ => h ▸ x j)

private theorem realize_instantiate (M : SortedStructure L E X) (v : ∀ s, W s → X s)
    (p : ∀ s, V s → W s) (x : Fin n → W .vf) (φ : SortedFormula L E (FBlock V n)) :
    (instantiate p x φ).realize M v ↔ φ.realize M (appendSortedBlock (fun s => v s ∘ p s) (v .vf ∘ x)) := by
  rw [instantiate,SortedFormula.realize_relabel]
  apply Iff.of_eq
  congr 1
  funext s j
  rcases j with j | ⟨j,⟨rfl⟩⟩ <;> rfl

private def onlyFields (φ : SortedFormula L E (FV.{u} m)) (x : Fin m → V .vf) := instantiate (fun _ => PEmpty.elim) x φ
abbrev fieldsAt (φ : SortedFormula L E (FV.{u} m)) (M : SortedStructure L E X) (x : Fin m → X .vf) :=
  φ.realize M (appendSortedBlock (fun _ => PEmpty.elim) x)

private theorem realize_onlyFields (M : SortedStructure L E X) (v : ∀ s, V s → X s)
    (φ : SortedFormula L E (FV.{u} m)) (x : Fin m → V .vf) :
    (onlyFields φ x).realize M v ↔ fieldsAt φ M (v .vf ∘ x) := by
  rw [onlyFields,realize_instantiate]
  have hp : (fun s => v s ∘ (PEmpty.elim : PEmpty.{u+1} → V s)) = (fun s => (PEmpty.elim : PEmpty.{u+1} → X s)) := by funext s z; exact z.elim
  rw [hp]

/-- The ternary membership relation used in both the product and its
image. Its arguments are the point, center and a field radius representative. -/
def sortedOpenDisc (minusOne : L.Term Empty) (F : FieldTerms (convexLanguage L)) : SortedFormula L E (FV.{u} 3) :=
  liftValuedFormula minusOne (discMemberFormula F false (.var (0 : Fin 3)) (.var 1) (.var 2))
    (Sum.elim (fun j => .var (fresh j)) Fin.elim0)

abbrev ballAt (ball : SortedFormula L E (FV.{u} 3)) (M : SortedStructure L E X) (c r : X .vf) : Set (X .vf) :=
  {y | fieldsAt ball M ![y,c,r]}

theorem sortedOpenDisc_canonical {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [L.Structure K] (O : ValuationSubring K) [L.Structure (Residue O)] (hO : IsOrderConvex O)
    (power : E → RV0 O → RV0 O) (minusOne : L.Term Empty) (hm : minusOne.realize (Empty.elim : Empty → K) = -1)
    (F : FieldTerms (convexLanguage L)) (hF : letI := convexStructure O L; InterpretsFieldTerms (K := K) F) (c b : K) :
    ballAt (sortedOpenDisc minusOne F) (canonicalStructure O hO power) c b = openDisc O c (O.valuation b) := by
  let M := canonicalStructure (L := L) O hO power
  let φ := discMemberFormula F false (.var (0 : Fin 3)) (.var 1) (.var 2)
  ext y
  change (liftValuedFormula minusOne φ _).realize M _ ↔ _
  rw [realize_liftValuedFormula,recoveredValuedStructure_canonical_eq O hO power minusOne hm]
  let := convexStructure O L
  have ev (w : Fin 0 → K) : BoundedFormula.Realize φ ![y,c,b] w ↔ y ∈ openDisc O c (O.valuation b) := by
    rw [Subsingleton.elim w default]
    exact realize_discMemberFormula O hF false _ _ _ _
  apply ev

abbrev cod (V : TCsort → Type u) (n : ℕ) := FBlock V (n+n)
private def productForm (ball : SortedFormula L E (FV.{u} 3)) : SortedFormula L E (FBlock (cod V n) n) :=
  SortedFormula.allOf (List.ofFn (fun i : Fin n => onlyFields ball
    ![fresh i,.inl (fresh (Fin.castAdd n i)),.inl (fresh (Fin.natAdd n i))]))

abbrev productAt (ball : SortedFormula L E (FV.{u} 3)) (M : SortedStructure L E X) (b : Fin (n+n) → X .vf) :=
  {x : Fin n → X .vf | ∀ i, x i ∈ ballAt ball M (b (Fin.castAdd n i)) (b (Fin.natAdd n i))}

private theorem product_eval (M : SortedStructure L E X) (p : ∀ s, cod V n s → X s)
    (ball : SortedFormula L E (FV.{u} 3)) (x : Fin n → X .vf) :
    (productForm ball).realize M (appendSortedBlock p x) ↔ x ∈ productAt ball M (p .vf ∘ fresh) := by
  simp only [productForm,SortedFormula.realize_allOf,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,realize_onlyFields]
  apply forall_congr'; intro j
  change fieldsAt ball M _ ↔ fieldsAt ball M _
  have eqn : (appendSortedBlock p x .vf ∘ ![fresh j,.inl (fresh (Fin.castAdd n j)),.inl (fresh (Fin.natAdd n j))]) =
      ![x j,p .vf (fresh (Fin.castAdd n j)),p .vf (fresh (Fin.natAdd n j))] := by funext k; fin_cases k <;> rfl
  rw [eqn]; rfl

private def imageForm (ball : SortedFormula L E (FV.{u} 3)) (G : SortedFormula L E (FBlock V (n+1)))
    (p : ∀ s, cod V n s → W s) (y : W .vf) : SortedFormula L E W :=
  let pts : SortedFormula L E (FBlock W n) := instantiate (fun s j => Sum.inl (p s j)) fresh (productForm ball)
  let graph : SortedFormula L E (FBlock W n) := instantiate (fun s j => Sum.inl (p s (.inl j))) (Fin.snoc fresh (.inl y)) G
  (pts.conjunction graph).exBlock .vf n

abbrev imageAt (M : SortedStructure L E X) (ball : SortedFormula L E (FV.{u} 3)) (G : SortedFormula L E (FBlock V (n+1)))
    (v : ∀ s, V s → X s) (b : Fin (n+n) → X .vf) : Set (X .vf) :=
  {y | ∃ x ∈ productAt ball M b, G.realize M (appendSortedBlock v (Fin.snoc x y))}

private theorem image_eval (M : SortedStructure L E X) (w : ∀ s, W s → X s)
    (ball : SortedFormula L E (FV.{u} 3)) (G : SortedFormula L E (FBlock V (n+1))) (p : ∀ s, cod V n s → W s) (y : W .vf) :
    (imageForm ball G p y).realize M w ↔ w .vf y ∈ imageAt M ball G
      (fun s j => w s (p s (.inl j))) (w .vf ∘ p .vf ∘ fresh) := by
  simp only [imageForm,SortedFormula.realize_exBlock,SortedFormula.realize_conjunction,realize_instantiate]
  apply exists_congr; intro x
  rw [product_eval]
  apply and_congr_right; intro _
  change G.realize M (appendSortedBlock _ (appendSortedBlock w x .vf ∘ Fin.snoc fresh (.inl y))) ↔ _
  have eqn : appendSortedBlock w x .vf ∘ Fin.snoc fresh (.inl y) = Fin.snoc x (w .vf y) := by
    funext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp only [Function.comp_apply,Fin.snoc_last,Fin.snoc_castSucc] <;> rfl
  rw [eqn]; rfl

/-- The concrete image condition in 3.16. Empty products of open
balls with an invalid (zero) radius are ignored. -/
def GoodDiscImage (M : SortedStructure L E X) (ball : SortedFormula L E (FV.{u} 3)) (S : Set (X .vf)) : Prop :=
  (∃ z, ∀ y ∈ S, M.rvMap y = M.rvMap z) ∧ ((∃ z, S = {z}) ∨ ∃ c r, S = ballAt ball M c r)

private def goodForm (ball : SortedFormula L E (FV.{u} 3)) (G : SortedFormula L E (FBlock V (n+1))) :
    SortedFormula L E (cod V n) :=
  let z : FBlock (cod V n) 2 .vf := fresh 0
  let r : FBlock (cod V n) 2 .vf := fresh 1
  let y : FBlock (FBlock (cod V n) 2) 1 .vf := fresh 0
  let im := imageForm ball G (fun _ j => .inl (.inl j)) y
  let eqv := fun a b : SortedFormula L E (FBlock (FBlock (cod V n) 2) 1) => (a.imp b).conjunction (b.imp a)
  let same := (im.imp (.equal (rvOf (.var y)) (rvOf (.var (.inl z))))).allBlock .vf 1
  let point := (eqv im (.equal (.var y) (.var (.inl z)))).allBlock .vf 1
  let disc := (eqv im (onlyFields ball ![y,.inl z,.inl r])).allBlock .vf 1
  (same.exBlock .vf 2).conjunction ((point.disjunction disc).exBlock .vf 2)

private theorem good_eval (M : SortedStructure L E X) (p : ∀ s, cod V n s → X s)
    (ball : SortedFormula L E (FV.{u} 3)) (G : SortedFormula L E (FBlock V (n+1))) :
    (goodForm ball G).realize M p ↔ GoodDiscImage M ball (imageAt M ball G
      (objectBaseAssignment p) (p .vf ∘ fresh)) := by
  let S := imageAt M ball G (objectBaseAssignment p) (p .vf ∘ fresh)
  change _ ↔ (∃ z, ∀ y ∈ S, M.rvMap y = M.rvMap z) ∧ ((∃ z, S = {z}) ∨ ∃ c r, S = ballAt ball M c r)
  simp only [goodForm,SortedFormula.realize_conjunction,SortedFormula.realize_disjunction,
    SortedFormula.realize_exBlock,SortedFormula.realize_allBlock,SortedFormula.realize,SortedTerm.realize,rvOf_realize,
    image_eval,realize_onlyFields]
  change ((∃ v : Fin 2 → X .vf, ∀ y : Fin 1 → X .vf, y 0 ∈ S → M.rvMap (y 0) = M.rvMap (v 0)) ∧
    ∃ v : Fin 2 → X .vf, (∀ y : Fin 1 → X .vf, (y 0 ∈ S → y 0 = v 0) ∧ (y 0 = v 0 → y 0 ∈ S)) ∨
      (∀ y : Fin 1 → X .vf, (y 0 ∈ S → _) ∧ (_ → y 0 ∈ S))) ↔ _
  apply and_congr
  · exact ⟨fun ⟨v,h⟩ => ⟨v 0,fun y => h (fun _ => y)⟩,fun ⟨z,h⟩ => ⟨fun _ => z,fun y => h (y 0)⟩⟩
  · have ev (v : Fin 2 → X .vf) (y : Fin 1 → X .vf) : fieldsAt ball M
        (appendSortedBlock (appendSortedBlock p v) y .vf ∘ ![fresh 0,.inl (fresh 0),.inl (fresh 1)]) ↔
        y 0 ∈ ballAt ball M (v 0) (v 1) := by
      have eqn : (appendSortedBlock (appendSortedBlock p v) y .vf ∘ ![fresh 0,.inl (fresh 0),.inl (fresh 1)]) = ![y 0,v 0,v 1] := by
        funext i; fin_cases i <;> rfl
      rw [eqn]; rfl
    simp only [ev]
    constructor
    · rintro ⟨v,h|h⟩
      · exact Or.inl ⟨v 0,Set.ext (fun y => ⟨(h (fun _ => y)).1,(h (fun _ => y)).2⟩)⟩
      · exact Or.inr ⟨v 0,v 1,Set.ext (fun y => ⟨(h (fun _ => y)).1,(h (fun _ => y)).2⟩)⟩
    · rintro (⟨z,h⟩|⟨c,r,h⟩)
      · exact ⟨fun _ => z,Or.inl (fun y => ⟨(Set.ext_iff.mp h (y 0)).mp,(Set.ext_iff.mp h (y 0)).mpr⟩)⟩
      · exact ⟨![c,r],Or.inr (fun y => ⟨(Set.ext_iff.mp h (y 0)).mp,(Set.ext_iff.mp h (y 0)).mpr⟩)⟩

/-- The disjoint finite partition for 3.16–3.17 with the full
point-or-open and constant-RV conclusions. In the pure-field case the
domain and every allowed test are pure, so each truth cell is pure. -/
theorem partition_polydisc_images (T : SortedTheory L E) (A : SortedFormula L E (FBlock V n))
    (G : SortedFormula L E (FBlock V (n+1))) (ball : SortedFormula L E (FV.{u} 3))
    (tests : Set (SortedFormula L E (FBlock V n)))
    (atomic : ∀ (P : T.PointedModel (cod V n)),
      let v := objectBaseAssignment P.point
      let b := P.point .vf ∘ fresh
      let D := productAt ball P.model b
      D.Nonempty → (∀ x ∈ D, A.realize P.model (appendSortedBlock v x)) →
      (∀ φ ∈ tests, ∀ x ∈ D, ∀ y ∈ D, φ.realize P.model (appendSortedBlock v x) ↔ φ.realize P.model (appendSortedBlock v y)) →
      GoodDiscImage P.model ball (imageAt P.model ball G v b)) :
    ∃ F : Finset (SortedFormula L E (FBlock V n)), (↑F : Set _) ⊆ tests ∧
      ∀ (M : SortedStructure L E X) (v : ∀ s, V s → X s) (_ : ∀ s, Nonempty (X s)) (_ : ∀ φ ∈ T, φ.realize M),
      let dom := {a | A.realize M (appendSortedBlock v a)}
      let piece := truthCell dom (fun φ => {a | φ.realize M (appendSortedBlock v a)}) F
      (∀ x ∈ dom, ∃! j, x ∈ piece j) ∧ (∀ j, BlockDefinable M v .vf (piece j)) ∧
      ∀ j b, (productAt ball M b).Nonempty → productAt ball M b ⊆ piece j →
        GoodDiscImage M ball (imageAt M ball G v b) := by
  classical
  let bad := ((productForm (V := V) (n := n) ball).exBlock .vf n).conjunction (goodForm ball G).neg
  obtain ⟨F,hF,partition⟩ := partition_of_object_types (X := X) T A (productForm ball) bad tests (by
    intro P inside uniform fail
    obtain ⟨ne,no⟩ := (SortedFormula.realize_conjunction _ _ _ _).mp fail
    obtain ⟨x,hx⟩ := (SortedFormula.realize_exBlock _ _ _ _).mp ne
    apply (SortedFormula.realize_neg _ _ _).mp no
    apply (good_eval _ _ _ _).mpr
    exact atomic P ⟨x,(product_eval _ _ _ _).mp hx⟩ (fun z hz => inside z ((product_eval _ _ _ _).mpr hz))
      (fun φ hφ a ha b hb => uniform φ hφ a b ((product_eval _ _ _ _).mpr ha) ((product_eval _ _ _ _).mpr hb)))
  refine ⟨F,hF,?_⟩
  intro M v hn hT dom piece
  obtain ⟨one,defP,yes⟩ := partition M v hn hT
  refine ⟨one,defP,fun j b ne sub => ?_⟩
  have forbid := yes j b (fun a ha => sub ((product_eval _ _ _ _).mp ha))
  by_contra no
  apply forbid
  apply (SortedFormula.realize_conjunction _ _ _ _).mpr
  exact ⟨(SortedFormula.realize_exBlock _ _ _ _).mpr (ne.imp (fun x hx => (product_eval _ _ _ _).mpr hx)),
    (SortedFormula.realize_neg _ _ _).mpr (fun h => no ((good_eval _ _ _ _).mp h))⟩

end GeneralizedEuler.Section3.DiscPartition
