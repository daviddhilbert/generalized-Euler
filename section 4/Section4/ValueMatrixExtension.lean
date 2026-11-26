module

public import Section4.LinearSignTransfer
public import Section4.DefinableValueFrames
import all Section4.LinearSignTransfer
import all Section4.DefinableValueFrames

/-! Interpreting field matrices on value tuples. Composition, left
inverses and linear identities survive the change of coefficient space. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.Polyhedral
open FirstOrder
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

def entries (A : (I → F) →ₗ[F] (J → F)) (j : J) (i : I) : F := by
  classical
  exact A (Pi.single i 1) j

def extendMatrix (A : (I → F) →ₗ[F] (J → F)) (x : I → V) (j : J) :=
  linearTest (entries A j) x

omit [Fintype J] in
theorem extendMatrix_field (A : (I → F) →ₗ[F] (J → F)) (x : I → F) : extendMatrix A x = A x := by
  classical
  have eq : (∑ i, x i • Pi.single i (1 : F)) = x := by
    funext j; rw [Finset.sum_apply,Finset.sum_eq_single j]
    · simp
    · intro i _ h; simp [Pi.single_eq_of_ne (Ne.symm h)]
    · simp
  conv_rhs => rw [← eq,map_sum]
  funext j; simp [extendMatrix,linearTest,entries,Finset.sum_apply,mul_comm]

omit [Fintype K] in
theorem extendMatrix_comp (A : (I → F) →ₗ[F] (J → F)) (B : (J → F) →ₗ[F] (K → F))
    (x : I → V) : extendMatrix (B.comp A) x = extendMatrix B (extendMatrix A x) := by
  classical
  have coeff (k : K) (i : I) : entries (B.comp A) k i = ∑ j, entries B k j * entries A j i := by
    have eq := congrFun (extendMatrix_field B (A (Pi.single i 1))) k
    simpa [entries,extendMatrix,linearTest] using eq.symm
  funext k
  simp only [extendMatrix,linearTest,coeff,Finset.sum_smul,Finset.smul_sum,smul_smul]
  exact Finset.sum_comm

theorem extendMatrix_id (x : I → V) : extendMatrix (LinearMap.id (R := F) (M := I → F)) x = x := by
  classical
  funext j
  change (∑ i, (Pi.single i (1 : F) : I → F) j • x i)=x j
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ h; simp [Pi.single_eq_of_ne (Ne.symm h)]
  · simp

theorem extendMatrix_leftInverse (A : (I → F) →ₗ[F] (J → F)) (inj : Function.Injective A) (x : I → V) :
    extendMatrix A.leftInverse (extendMatrix A x) = x := by
  rw [← extendMatrix_comp,A.leftInverse_comp_of_inj (LinearMap.ker_eq_bot.mpr inj),extendMatrix_id]

theorem extendMatrix_injective (A : (I → F) →ₗ[F] (J → F)) (inj : Function.Injective A) :
    Function.Injective (extendMatrix (V := V) A) := Function.LeftInverse.injective (extendMatrix_leftInverse A inj)

omit [Fintype J] in
theorem extendMatrix_old (G : Submodule F V) (A : (I → F) →ₗ[F] (J → F)) (x : I → V)
    (old : ∀ i, x i ∈ G) (j : J) : extendMatrix A x j ∈ G :=
  G.sum_mem (fun i _ => G.smul_mem _ (old i))

omit [Fintype J] in
theorem extendMatrix_definable {L : Language} [L.Structure V] (G : Submodule F V)
    (lang : ValueLanguage (J := L) G) (A : (I → F) →ₗ[F] (J → F)) : (G : Set V).DefinableMap L (extendMatrix A) :=
  fun i => lang.row (entries A i)

end GeneralizedEuler.Section4.Polyhedral
