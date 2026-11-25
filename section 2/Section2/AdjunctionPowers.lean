module

public import Section2.CanonicalEmbedding
public import Section2.FieldOperations
public import Section2.FieldDefinableClosure

/-! Restriction of the named field and leading-term powers to the
elementary fields used in a one-generator adjunction. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder FirstOrder.Language

universe u v w

variable {L : Language.{u, v}} {E : Type w} [Field E]
  {J K : Type*} [Field J] [LinearOrder J] [IsStrictOrderedRing J] [L.Structure J]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]

/-- The scalar laws of the named positive field powers, with their
parameter-free definitions in the field language. -/
structure NamedFieldPowers (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [L.Structure K]
    (graph : E → L.Formula (Fin 2)) where
  pow : E → PositiveField K →* PositiveField K
  defines : ∀ e (v : Fin 2 → K), (graph e).Realize v ↔ totalFieldPower (pow e) (v 0) = v 1
  zero : ∀ x, pow 0 x = 1
  one : ∀ x, pow 1 x = x
  add : ∀ e d x, pow (e + d) x = pow e x * pow d x
  mul : ∀ e d x, pow (e * d) x = pow e (pow d x)

/-- The accompanying RV powers and preservation of valuation units. -/
structure NamedRVPowers (O : ValuationSubring K) (g : E → PositiveField K →* PositiveField K) where
  pow : E → RV0 O → RV0 O
  agrees : ∀ e, AgreesWithFieldPower O (g e) (pow e)
  offPositive : ∀ e t, ¬IsPositiveRV O t → pow e t = 0
  units : ∀ e (x : PositiveField K), O.valuation (x : K) = 1 → O.valuation (g e x : K) = 1

variable {graph : E → L.Formula (Fin 2)}
  (i : J ↪ₑ[L] K) (f : J →+* K) (hi : ∀ x, i x = f x) (hmono : StrictMono f)

include hi hmono in
/-- Restriction preserves the full set of scalar laws. The formula for
each ambient power specifies its restriction uniquely. -/
theorem exists_namedFieldPowers_of_elementary (ambient : NamedFieldPowers K graph) :
    Nonempty (NamedFieldPowers J graph) := by
  have hex (e : E) := exists_fieldPower_of_elementary i f hi hmono
    (ambient.pow e) (graph e) (ambient.defines e)
  choose g hg using hex
  let pos (x : PositiveField J) : PositiveField K := ⟨f x, (map_zero f) ▸ hmono x.property⟩
  have hc (e : E) (x : PositiveField J) : pos (g e x) = ambient.pow e (pos x) := by
    apply Subtype.ext
    change f (g e x : J) = (ambient.pow e (pos x) : K)
    rw [← hi]
    exact fieldPower_agrees_of_elementary i (g e) (ambient.pow e) (graph e) (hg e)
      (ambient.defines e) x (pos x) (hi x).symm
  have hinj : Function.Injective pos := fun _ _ h => Subtype.ext (f.injective (congrArg Subtype.val h))
  refine ⟨{ pow := g, defines := hg, zero := ?_, one := ?_, add := ?_, mul := ?_ }⟩
  · intro x
    apply hinj
    rw [hc, ambient.zero]
    exact Subtype.ext (map_one f).symm
  · intro x
    apply hinj
    rw [hc, ambient.one]
  · intro e d x
    apply hinj
    rw [hc, ambient.add]
    have hp (r s : PositiveField J) : pos (r * s) = pos r * pos s :=
      Subtype.ext (map_mul f (r : J) (s : J))
    rw [hp, hc, hc]
  · intro e d x
    apply hinj
    rw [hc, ambient.mul, hc, hc]

include hi hmono in
/-- Once the field powers are restricted, the corresponding leading
terms descend along any of the pulled-back valuations. -/
theorem exists_namedRVPowers_of_valued_embedding
    (g : NamedFieldPowers J graph) (ambient : NamedFieldPowers K graph)
    (I : ValuationSubring J) (O : ValuationSubring K) (hf : RespectsValuationRing I O f)
    (rvAmbient : NamedRVPowers O ambient.pow) :
    Nonempty (NamedRVPowers I g.pow) := by
  have hp (e : E) (x : PositiveField J) (y : PositiveField K) (hy : (y : K) = f x) :
      f (g.pow e x : J) = (ambient.pow e y : K) := by
    rw [← hi]
    exact fieldPower_agrees_of_elementary i (g.pow e) (ambient.pow e) (graph e) (g.defines e)
      (ambient.defines e) x y (hy.trans (hi _).symm)
  have hex (e : E) := (existsUnique_leadingTermPower_of_valued_embedding I O f hf hmono
    (g.pow e) (ambient.pow e) (rvAmbient.pow e) (rvAmbient.agrees e) (hp e)).exists
  choose p h using hex
  exact ⟨{ pow := p
           agrees := fun e => (h e).1
           offPositive := fun e => (h e).2
           units := fun e => fieldPower_preserves_units_of_valued_embedding I O f hf hmono
             (g.pow e) (ambient.pow e) (hp e) (rvAmbient.units e) }⟩

set_option linter.style.haveILetI false in
/-- Any field-language substructure is closed under the restricted
field powers in a universal field theory with QE. -/
theorem namedFieldPowers_mem_substructure
    (terms : OrderedFieldTerms L) (hJ : InterpretsOrderedFieldTerms (A := J) terms)
    {T : L.Theory} [T.IsUniversal] [J ⊨ T] (hQE : EliminatesQuantifiers T)
    (g : NamedFieldPowers J graph) (A : L.Substructure J)
    (e : E) (x : PositiveField J) (hx : (x : J) ∈ A) : (g.pow e x : J) ∈ A := by
  letI := fieldOnFieldSubstructure terms hJ A
  letI := strictOrderedRingOnFieldSubstructure terms hJ A
  let j : A ↪ₑ[L] J := elementaryEmbeddingOfQE hQE A.subtype
  let p := ringInclusionOfFieldSubstructure terms hJ A
  have hj (x : A) : j x = p x := (ringInclusionOfFieldSubstructure_apply terms hJ A x).symm
  have hm : StrictMono p := by
    intro x y h
    rw [ringInclusionOfFieldSubstructure_apply, ringInclusionOfFieldSubstructure_apply]
    exact h
  obtain ⟨gA⟩ := exists_namedFieldPowers_of_elementary j p hj hm g
  let a : A := ⟨x.val, hx⟩
  have ha : p 0 < p a := by
    rw [map_zero, ringInclusionOfFieldSubstructure_apply]
    exact x.property
  let y : PositiveField A := ⟨a, hm.lt_iff_lt.mp ha⟩
  have hy : (x : J) = j y := rfl
  have he := fieldPower_agrees_of_elementary j (gA.pow e) (g.pow e) (graph e) (gA.defines e)
    (g.defines e) y x hy
  exact he ▸ (gA.pow e y).val.property

end GeneralizedEuler.Section2
