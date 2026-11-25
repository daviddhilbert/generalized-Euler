module

public import Section2.SortedModelTheory

/-! The VF-generated part of a two-sorted structure and uniqueness of
embeddings on that part. -/

public section

namespace GeneralizedEuler.Section2

open FirstOrder

universe u v w z z'

variable {L : Language.{u, v}} {E : Type w} {X : TCsort → Type z}
  {Y : TCsort → Type z'} (M : SortedStructure L E X) {N : SortedStructure L E Y}

private def vfArgument (x : X .vf) : SortedArgs X [.vf] :=
  fun i => by
    have hi : i = 0 := Fin.fin_one_eq_zero (i : Fin 1)
    subst i
    exact x

/-- The leading-term symbol in an abstract sorted structure. -/
def SortedStructure.rvMap (x : X .vf) : X .rv :=
  M.funMap (.rv : FunctionSymbol L E [.vf] .rv) (vfArgument x)

theorem SortedEmbedding.map_rv {M : SortedStructure L E X} (e : SortedEmbedding M N)
    (x : X .vf) :
    e.toEmbedding .rv (M.rvMap x) = N.rvMap (e.toEmbedding .vf x) := by
  unfold SortedStructure.rvMap
  rw [e.map_fun]
  congr 1
  funext i
  have hi : i = 0 := Fin.fin_one_eq_zero (i : Fin 1)
  subst i
  rfl

/-- A substructure is VF-generated if every RV element has a field
representative in that substructure. -/
def SortedStructure.IsVFGenerated : Prop :=
  Function.Surjective M.rvMap

/-- Agreement on VF forces agreement on both sorts for a VF-generated
substructure, including ones with trivial valuation. -/
theorem SortedEmbedding.ext_of_vf_generated (h : M.IsVFGenerated)
    (i j : SortedEmbedding M N) (hVF : ∀ x : X .vf, i.toEmbedding .vf x = j.toEmbedding .vf x) :
    ∀ s (x : X s), i.toEmbedding s x = j.toEmbedding s x := by
  intro s x
  cases s with
  | vf => exact hVF x
  | rv =>
    obtain ⟨y, rfl⟩ := h x
    rw [i.map_rv, j.map_rv, hVF]

end GeneralizedEuler.Section2
