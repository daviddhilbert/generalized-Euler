module

public import Section4.GraphCharts
public import Section2.RVFormulaSeparation

/-! Disjoint refinement of separated formulas and the residue factor of an
affine value cell. The splitting section is used only in the proof. -/
public section
noncomputable section
namespace GeneralizedEuler.Section4
open GeneralizedEuler.Section2

/-- Truth-pattern cells in the value sort and the corresponding residue
sets. Each nonempty cell retains predicates over the given parameter base. -/
theorem separated_partition {A B : Type*} {P : Set A → Prop} {Q : Set B → Prop}
    (pu : P Set.univ) (pi : ∀ {s t}, P s → P t → P (s ∩ t))
    (pc : ∀ {s}, P s → P sᶜ) (qe : Q ∅) (qu : ∀ {s t}, Q s → Q t → Q (s ∪ t))
    {D : Set (A × B)} (h : SeparatedSets P Q D) :
    ∃ (n : ℕ) (V : Fin n → Set A) (B' : Fin n → Set B),
      (∀ i, P (V i) ∧ Q (B' i)) ∧ (∀ a, ∃! i, a ∈ V i) ∧
      ∀ a b i, a ∈ V i → ((a,b) ∈ D ↔ b ∈ B' i) := by
  classical
  induction h with
  | empty =>
    exact ⟨1,fun _ => Set.univ,fun _ => ∅,fun _ => ⟨pu,qe⟩,
      fun _ => ⟨0,Set.mem_univ _,fun j _ => Subsingleton.elim j 0⟩, fun _ _ _ _ => Iff.rfl⟩
  | @insert U V D hU hV _ ih =>
    obtain ⟨n,A,B,hAB,unique,cells⟩ := ih
    let e := finSumFinEquiv (m := n) (n := n)
    let vs : Fin n ⊕ Fin n → Set _ := Sum.elim (fun i => A i ∩ U) (fun i => A i ∩ Uᶜ)
    let bs : Fin n ⊕ Fin n → Set _ := Sum.elim (fun i => V ∪ B i) B
    refine ⟨n+n,vs ∘ e.symm,bs ∘ e.symm,?_,?_,?_⟩
    · intro i
      change P (vs (e.symm i)) ∧ Q (bs (e.symm i))
      rcases e.symm i with i | i
      · exact ⟨pi (hAB i).1 hU,qu hV (hAB i).2⟩
      · exact ⟨pi (hAB i).1 (pc hU),(hAB i).2⟩
    · intro a
      obtain ⟨i,hi,uniq⟩ := unique a
      let idx : Fin n ⊕ Fin n := if a ∈ U then .inl i else .inr i
      refine ⟨e idx, ?_, ?_⟩
      · simp only [Function.comp_apply,Equiv.symm_apply_apply]
        by_cases ha : a ∈ U <;> simp [idx,ha,vs,hi]
      · intro j hj
        apply e.symm.injective
        rw [Equiv.symm_apply_apply]
        change a ∈ vs (e.symm j) at hj
        rcases he : e.symm j with t | t <;> rw [he] at hj
        · simp [idx, show a ∈ U from hj.2,uniq t hj.1]
        · simp [idx, show a ∉ U from hj.2,uniq t hj.1]
    · intro a b i hi
      change a ∈ vs (e.symm i) at hi
      change _ ↔ b ∈ bs (e.symm i)
      rcases he : e.symm i with i | i <;> rw [he] at hi
      · exact (or_congr (and_iff_right hi.2) (cells a b i hi.1))
      · change (a ∈ U ∧ b ∈ V ∨ (a,b) ∈ D) ↔ b ∈ B i
        simp [show a ∉ U from hi.2,cells a b i hi.1]

section Cell
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T]
  [AddCommGroup V] [Module F V] {i j : Type*} [Fintype i]

def splitUnit (v : T →ₗ[F] V) (s : V →ₗ[F] T) (hs : v.comp s = LinearMap.id) (t : T) :
    v.ker := ⟨t - s (v t), by
      change v _ = 0
      rw [map_sub,show v (s (v t)) = v t from DFunLike.congr_fun hs _, sub_self]⟩

theorem affine_cell_residue (v : T →ₗ[F] V) (G : Submodule F V) (s : V →ₗ[F] T)
    (hs : v.comp s = LinearMap.id) (A : Matrix j i F) (u : j → T) (hu : ∀ k, v (u k) ∈ G)
    (D : Set (i → V)) (α : i → V) (hα : α ∈ D) (hi : LinearIndependent F (G.mkQ ∘ α))
    (U : Set (i ⊕ j → T)) (invariant : ∀ L x, x ∈ U → shear v G L ∘ x ∈ U)
    (R : (i → v.ker) → (j → v.ker) → Prop)
    (cell : ∀ z, v ∘ z ∈ D → ∀ b : j → v.ker,
      chartPoint A u z (fun k => (b k).val) ∈ U ↔ R (splitUnit v s hs ∘ z) b) :
    ∀ z, v ∘ z ∈ D → ∀ b : j → v.ker,
      chartPoint A u z (fun k => (b k).val) ∈ U ↔ R 0 b := by
  apply fun z hz b => (cell z hz b).trans ?_
  apply cell_product v G s hs α hi R _ _ _
  intro L a b ha
  let t (k : i) := s (α k) + (a k).val
  have ht (k) : v (t k) = α k := by
    change v (_ + _) = _
    rw [map_add,show v (a k).val = 0 from (a k).property,add_zero]
    exact DFunLike.congr_fun hs _
  have hvt : v ∘ t = α := funext ht
  have ht' : v ∘ t ∈ D := hvt.symm ▸ hα
  have unit : splitUnit v s hs ∘ t = a := by
    funext k; apply Subtype.ext; change t k - s (v (t k)) = _
    rw [ht]; exact add_sub_cancel_left _ _
  have h := invariant L _ ((cell _ ht' b).mpr (unit.symm ▸ ha))
  let e := shear v G L
  have acted : e ∘ chartPoint A u t (fun k => (b k).val) =
      chartPoint A u (e ∘ t) (fun k => (b k).val) := by
    funext k; cases k with
    | inl => rfl
    | inr k =>
      change e (_ + _ + _) = _ + _ + _
      rw [map_add,map_add,show e (u k) = u k from shear_fixes_base v G L (hu k)]
      have hb : e (b k).val = (b k).val := shear_fixes_base v G L ((b k).property ▸ G.zero_mem)
      rw [hb]
      exact congrArg (fun t => (b k).val + t + u k) (congrFun (actRows_map e.toLinearMap A t) k)
  rw [acted] at h
  have hv (k) : v (e (t k)) = α k := (shear_preserves_value v G L _).trans (ht k)
  have hve : v ∘ (e ∘ t) = α := funext hv
  have hr := (cell (e ∘ t) (hve.symm ▸ hα) b).mp h
  suffices eq : (fun k => a k + L (G.mkQ (α k))) = splitUnit v s hs ∘ (e ∘ t) from eq.symm ▸ hr
  funext k
  apply Subtype.ext
  change (a k).val + (L (G.mkQ (α k))).val = e (t k) - s (v (e (t k)))
  rw [hv,show e (t k) = t k + (L (G.mkQ (v (t k)))).val from rfl,ht]
  dsimp [t]; abel

end Cell
end GeneralizedEuler.Section4
