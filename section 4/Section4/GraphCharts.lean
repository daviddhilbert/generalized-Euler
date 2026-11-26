module

public import Section4.AffineLifts
public import Section4.FiberMatching

/-! On an affine value cell, an independent tuple in the cell removes the
dependence of the residue tests on the free representatives. -/

public section
noncomputable section
namespace GeneralizedEuler.Section4
variable {F T V : Type*} [Field F] [AddCommGroup T] [Module F T]
  [AddCommGroup V] [Module F V] {i j : Type*} [Fintype i]

omit [Fintype i] in
/-- In split coordinates, fix a value cell and its residue predicate.
The coordinates are the free and the normalized dependent coordinates.
The latter are fixed by a shear. -/
theorem cell_product (v : T →ₗ[F] V) (G : Submodule F V) (s : V →ₗ[F] T)
    (hs : v.comp s = LinearMap.id) (α : i → V) (hi : LinearIndependent F (G.mkQ ∘ α))
    (R : (i → v.ker) → (j → v.ker) → Prop)
    (hinv : ∀ (L : (V ⧸ G) →ₗ[F] v.ker) a b, R a b →
      R (fun k => a k + L (G.mkQ (α k))) b) :
    ∀ a b, R a b ↔ R 0 b := by
  have hv (a : i → v.ker) : v ∘ (fun k => s (α k) + (a k).val) = α := by
    funext k
    change v (_ + _) = _
    rw [map_add, (a k).property, add_zero]
    exact DFunLike.congr_fun hs _
  have transport (a c : i → v.ker) (b : j → v.ker) (ha : R a b) : R c b := by
    let x (k : i) := s (α k) + (a k).val
    let y (k : i) := s (α k) + (c k).val
    have hx : v ∘ x = α := hv a
    have hy : v ∘ y = α := hv c
    obtain ⟨L,hL⟩ := transitive_independent_fiber v G x y (hx.symm ▸ hi) (hx.trans hy.symm)
    have he : (fun k => a k + L (G.mkQ (α k))) = c := by
      funext k
      apply Subtype.ext
      have hk := congrFun hL k
      change (s (α k) + (a k).val) + (L (G.mkQ (v (x k)))).val = s (α k) + (c k).val at hk
      rw [show v (x k) = α k from congrFun hx k, add_assoc] at hk
      exact add_left_cancel hk
    exact he ▸ hinv L a b ha
  exact fun a b => ⟨transport a 0 b, transport 0 a b⟩

/-- Lift one scalar direction of the affine hull into a fixed residue fiber.
Coordinates in the kernel of a projection keep their original leading terms. -/
def chartDirection (A : Matrix j i F) (w : i → F) : i ⊕ j → F :=
  Sum.elim w (actRows A w)

@[expose] def chartPoint (A : Matrix j i F) (u : j → T) (z : i → T) (b : j → T) : i ⊕ j → T :=
  Sum.elim z (fun k => b k + actRows A z k + u k)

theorem chartPoint_translate (A : Matrix j i F) (u : j → T) (z : i → T) (b : j → T)
    (w : i → F) (d : T) (k : i ⊕ j) :
    chartPoint A u (fun l => z l + w l • d) b k =
      chartPoint A u z b k + chartDirection A w k • d := by
  cases k with
  | inl => rfl
  | inr k =>
    simp only [chartPoint, chartDirection, Sum.elim_inr, actRows, smul_add, Finset.sum_add_distrib,
      smul_smul, smul_eq_mul, Finset.sum_smul]
    abel

/-- The graph rank argument. An injective coordinate projection on a
nonempty chart is injective on the directions of its value cell. -/
theorem graph_projection_directions {κ : Type*} (v : T →ₗ[F] V) (A : Matrix j i F)
    (u : j → T) (z : i → T) (b : j → T) (D : Set (i ⊕ j → T)) (π : κ → i ⊕ j)
    (inside : ∀ z', v ∘ z' = v ∘ z → chartPoint A u z' b ∈ D)
    (inj : Set.InjOn (fun x : i ⊕ j → T => x ∘ π) D)
    (d : v.ker) (hd : d ≠ 0) (w : i → F) (hw : ∀ l, chartDirection A w (π l) = 0) :
    w = 0 := by
  let z' (k : i) := z k + w k • d.val
  have hz' : v ∘ z' = v ∘ z := by funext k; simp [z']
  have img : chartPoint A u z' b ∘ π = chartPoint A u z b ∘ π := by
    funext k
    simp [Function.comp_apply, z', chartPoint_translate, hw]
  have full := inj (inside z' hz') (inside z rfl) img
  funext k
  have hk := congrFun full (.inl k)
  change z k + w k • d.val = z k at hk
  have hdz : (d : T) ≠ 0 := fun h => hd (Subtype.ext h)
  exact (smul_eq_zero.mp (add_eq_left.mp hk)).resolve_right hdz

/-- Fixing one free tuple identifies the projected residue set with the
residue set of an injectively projected graph chart. -/
def projectedResidues {A B C : Type*} (D : Set A) (hD : D.Nonempty) (U : Set B)
    (p : B → C) (h : Set.InjOn (fun x : A × B => (x.1,p x.2)) (D ×ˢ U)) :
    U ≃ (p '' U) := by
  apply Equiv.Set.imageOfInjOn
  intro b hb b' hb' he
  obtain ⟨z,hz⟩ := hD
  exact congrArg Prod.snd (h (x₁ := (z,b)) ⟨hz,hb⟩ (x₂ := (z,b')) ⟨hz,hb'⟩ (Prod.ext rfl he))

end GeneralizedEuler.Section4
