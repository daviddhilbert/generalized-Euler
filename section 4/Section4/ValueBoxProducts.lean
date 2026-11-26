module

public import Section4.ValueScissors
import all Section4.ValueScissors
import all Section4.Factors

/-! A Cartesian box in a fixed ambient degree has class the product
of its unary classes. This includes padded coordinates and the empty
product in degree zero. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4.ValueObject
open FirstOrder Set
variable {V : Type*} {J : Language} [J.Structure V] (G : Set V)

def coordinateBox {k} (d : Fin k → Set (Fin 1 → V)) : Set (Fin k → V) :=
  {x | ∀ i, (fun _ => x i) ∈ d i}

theorem coordinateBox_definable {k} {d : Fin k → Set (Fin 1 → V)} (hd : ∀ i, G.Definable J (d i)) :
    G.Definable J (coordinateBox d) := by
  convert Set.definable_iInter_of_finite (fun i => (hd i).preimage_comp (fun _ : Fin 1 => i)) using 1
  ext x; simp [coordinateBox,Function.comp_def]

theorem coordinateBox_class {k} (d : Fin k → Set (Fin 1 → V)) (hd : ∀ i, G.Definable J (d i)) :
    pieceClass (coordinateBox d) (coordinateBox_definable G hd) = ∏ i, pieceClass _ (hd i) := by
  induction k with
  | zero =>
    let z : Fin 0 → V := Fin.elim0
    have eq : coordinateBox d = {z} := by ext x; simp [coordinateBox,Subsingleton.elim x z]
    have dz : G.Definable J {z} := eq ▸ coordinateBox_definable G hd
    calc pieceClass _ _ = pieceClass _ dz := by congr 1
         _ = _ := by rw [pieceClass_degree_zero z dz]; simp
  | succ k ih =>
    let first (i : Fin k) := d i.castSucc
    let last := d (Fin.last k)
    have df := coordinateBox_definable G (fun i : Fin k => hd i.castSucc)
    have dl := hd (Fin.last k)
    have eq : coordinateBox d = cartesian (coordinateBox first) last := by
      ext x
      change (∀ i : Fin (k+1), (fun _ : Fin 1 => x i) ∈ d i) ↔
        (∀ i : Fin k, (fun _ : Fin 1 => x i.castSucc) ∈ d i.castSucc) ∧
        (x ∘ (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k+1)) ∘ Sum.inr) ∈ last
      have endEq : x ∘ (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k+1)) ∘ Sum.inr =
          (fun _ : Fin 1 => x (Fin.last k)) := funext (fun i => by fin_cases i; rfl)
      rw [endEq]
      exact ⟨fun h => ⟨fun i => h i.castSucc,h _⟩,fun h => Fin.lastCases h.2 h.1⟩
    calc pieceClass _ _ = pieceClass _ (cartesian_definable df dl) := by congr 1
         _ = _ := by rw [pieceClass_product df dl,ih first (fun i => hd i.castSucc),Fin.prod_univ_castSucc]

end GeneralizedEuler.Section4.ValueObject
