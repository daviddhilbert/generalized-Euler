module

public import Section2.DirectedSubstructure

/-! Transport of the prescribed-RV extension property across sorted
isomorphisms. -/

public section

noncomputable section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w x y z

variable {L : Language.{u, v}} {E : Type w}
  {X : TCsort → Type x} {Y : TCsort → Type y} {Z : TCsort → Type z}
  {M : SortedStructure L E X} {N : SortedStructure L E Y} {P : SortedStructure L E Z}

/-- Composition in the sorted language. -/
@[expose]
def SortedEmbedding.comp (g : SortedEmbedding N P) (f : SortedEmbedding M N) : SortedEmbedding M P where
  toEmbedding s := ⟨g.toEmbedding s ∘ f.toEmbedding s,
    (g.toEmbedding s).injective.comp (f.toEmbedding s).injective⟩
  map_fun symbol a := by
    change g.toEmbedding _ (f.toEmbedding _ (M.funMap symbol a)) = _
    rw [f.map_fun, g.map_fun]
    rfl
  map_rel symbol a := (g.map_rel symbol (fun i => f.toEmbedding _ (a i))).trans (f.map_rel symbol a)

/-- The inverse embedding of an isomorphism. -/
@[expose]
def SortedIsomorphism.symm (i : SortedIsomorphism M N) : SortedIsomorphism N M := by
  let e (s : TCsort) := Equiv.ofBijective (i.toEmbedding s) ⟨(i.toEmbedding s).injective, i.surjective s⟩
  refine {
    toEmbedding := fun s => (e s).symm.toEmbedding
    surjective := fun s => (e s).symm.surjective
    map_fun := ?_
    map_rel := ?_ }
  · intro ss s f a
    change (e s).symm (N.funMap f a) = M.funMap f (fun j => (e _).symm (a j))
    apply (e s).injective
    rw [Equiv.apply_symm_apply]
    change N.funMap f a = i.toEmbedding s (M.funMap f (fun j => (e _).symm (a j)))
    rw [i.map_fun]
    congr 1
    funext j
    exact ((e _).apply_symm_apply (a j)).symm
  · intro ss r a
    change M.relMap r (fun j => (e _).symm (a j)) ↔ N.relMap r a
    have h := i.map_rel r (fun j => (e _).symm (a j))
    rw [show (fun j => i.toEmbedding _ ((e _).symm (a j))) = a from
      funext (fun j => (e _).apply_symm_apply (a j))] at h
    exact h.symm

@[simp]
theorem SortedIsomorphism.symm_apply_apply (i : SortedIsomorphism M N) (s : TCsort) (a : X s) :
    i.symm.toEmbedding s (i.toEmbedding s a) = a :=
  (Equiv.ofBijective (i.toEmbedding s) ⟨(i.toEmbedding s).injective, i.surjective s⟩).symm_apply_apply a

@[simp]
theorem SortedIsomorphism.apply_symm_apply (i : SortedIsomorphism M N) (s : TCsort) (a : Y s) :
    i.toEmbedding s (i.symm.toEmbedding s a) = a :=
  (Equiv.ofBijective (i.toEmbedding s) ⟨(i.toEmbedding s).injective, i.surjective s⟩).apply_symm_apply a

/-- The preimage of a sorted substructure under a sorted embedding. -/
@[expose]
def SortedSubstructure.comapEmbedding (S : SortedSubstructure N) (i : SortedEmbedding M N) :
    SortedSubstructure M where
  carrier s := i.toEmbedding s ⁻¹' S.carrier s
  closed := by
    intro ss s f a ha
    change i.toEmbedding s (M.funMap f a) ∈ S.carrier s
    rw [i.map_fun]
    exact S.closed f (fun j => i.toEmbedding _ (a j)) ha

/-- The embedding of a pullback substructure in the original substructure. -/
@[expose]
def SortedSubstructure.embeddingOfComap (S : SortedSubstructure N) (i : SortedEmbedding M N) :
    SortedEmbedding (S.comapEmbedding i).structureOn S.structureOn where
  toEmbedding s := ⟨fun a => ⟨i.toEmbedding s a.val, a.property⟩,
    fun _ _ hab => Subtype.ext ((i.toEmbedding s).injective (congrArg Subtype.val hab))⟩
  map_fun f a := Subtype.ext (i.map_fun f (fun j => (a j).val))
  map_rel r a := i.map_rel r (fun j => (a j).val)

variable {W : TCsort → Type*} {Q : SortedStructure L E W}

namespace FixedRVLift

/-- Pulling a lift back across a source embedding and mapping its
images by a target embedding respects its fixed RV sort. -/
@[expose]
def transport {R : Set (X .rv)} (A : FixedRVLift M N R)
    (i : SortedEmbedding P M) (j : SortedEmbedding N Q) :
    FixedRVLift P Q (i.toEmbedding .rv ⁻¹' R) :=
  ⟨A.source.comapEmbedding i, congrArg (i.toEmbedding .rv ⁻¹' ·) A.rv_eq,
    j.comp (A.embedding.comp (A.source.embeddingOfComap i))⟩

theorem transport_mono {R : Set (X .rv)} {A B : FixedRVLift M N R} (h : A ≤ B)
    (i : SortedEmbedding P M) (j : SortedEmbedding N Q) :
    A.transport i j ≤ B.transport i j := by
  obtain ⟨hm, he⟩ := (FixedRVLift.le_iff_extends A B).mp h
  apply FixedRVLift.le_of_compatible (A := A.transport i j) (B := B.transport i j)
    (fun s _ hx => hm s hx)
  intro s a
  exact congrArg (j.toEmbedding s) (he s ⟨i.toEmbedding s a.val, a.property⟩)

/-- The existence of a fixed-RV adjunction for one pair of models
carries across isomorphisms of both models. -/
theorem exists_extension_of_isomorphic_step {R : Set (X .rv)} (A : FixedRVLift M N R)
    (i : SortedIsomorphism M P) (j : SortedIsomorphism N Q)
    (t : X .rv) (ht : t ∈ R) (hNew : t ∉ M.rvMap '' A.source.carrier .vf)
    (step : ∀ {S : Set (Z .rv)} (B : FixedRVLift P Q S) (p : Z .rv),
      p ∈ S → p ∉ P.rvMap '' B.source.carrier .vf →
      ∃ C : FixedRVLift P Q S, B ≤ C ∧ p ∈ P.rvMap '' C.source.carrier .vf) :
    ∃ C : FixedRVLift M N R, A ≤ C ∧ t ∈ M.rvMap '' C.source.carrier .vf := by
  let B := A.transport i.symm.toSortedEmbedding j.toSortedEmbedding
  have ht' : i.toEmbedding .rv t ∈ i.symm.toEmbedding .rv ⁻¹' R := by
    change i.symm.toEmbedding .rv (i.toEmbedding .rv t) ∈ R
    rwa [i.symm_apply_apply]
  have hn' : i.toEmbedding .rv t ∉ P.rvMap '' B.source.carrier .vf := by
    rintro ⟨x, hx, he⟩
    have hx' : i.symm.toEmbedding .vf x ∈ A.source.carrier .vf := hx
    have he' := i.symm.toSortedEmbedding.map_rv x
    rw [he, i.symm_apply_apply] at he'
    exact hNew ⟨i.symm.toEmbedding .vf x, hx', he'.symm⟩
  obtain ⟨D, hBD, x, hx, he⟩ := step B (i.toEmbedding .rv t) ht' hn'
  have hR : i.toEmbedding .rv ⁻¹' (i.symm.toEmbedding .rv ⁻¹' R) = R := by
    ext s
    change i.symm.toEmbedding .rv (i.toEmbedding .rv s) ∈ R ↔ s ∈ R
    rw [i.symm_apply_apply]
  let D' := D.transport i.toSortedEmbedding j.symm.toSortedEmbedding
  let C : FixedRVLift M N R := ⟨D'.source, D'.rv_eq.trans hR, D'.embedding⟩
  have hmem (s : TCsort) (p : X s) (hp : p ∈ A.source.carrier s) :
      i.toEmbedding s p ∈ B.source.carrier s := by
    change i.symm.toEmbedding s (i.toEmbedding s p) ∈ A.source.carrier s
    rwa [i.symm_apply_apply]
  obtain ⟨hDom, hMap⟩ := (FixedRVLift.le_iff_extends B D).mp hBD
  refine ⟨C, ?_, i.symm.toEmbedding .vf x, ?_, ?_⟩
  · apply FixedRVLift.le_of_compatible (A := A) (B := C)
      (fun s p hp => hDom s (hmem s p hp))
    intro s p
    have heq := hMap s ⟨i.toEmbedding s p.val, hmem s p.val p.property⟩
    change j.toEmbedding s
      (A.embedding.toEmbedding s ⟨i.symm.toEmbedding s (i.toEmbedding s p.val), _⟩) = _ at heq
    change A.embedding.toEmbedding s p =
      j.symm.toEmbedding s (D.embedding.toEmbedding s ⟨i.toEmbedding s p.val, _⟩)
    rw [← heq, j.symm_apply_apply]
    congr 1
    exact Subtype.ext (i.symm_apply_apply s p.val).symm
  · change i.toEmbedding .vf (i.symm.toEmbedding .vf x) ∈ D.source.carrier .vf
    rwa [i.apply_symm_apply]
  · have heq := i.symm.toSortedEmbedding.map_rv x
    rw [he, i.symm_apply_apply] at heq
    exact heq.symm

end FixedRVLift

end GeneralizedEuler.Section2
