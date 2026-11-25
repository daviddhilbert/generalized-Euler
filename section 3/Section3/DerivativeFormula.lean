module

public import Section3.ResidueInterval
public import Section2.ContinuousDefinitions
import all Section2.ContinuousDefinitions
import all Section2.TorsorDerivative

public section

namespace GeneralizedEuler.Section3

open Set GeneralizedEuler.Section2 FirstOrder FirstOrder.Language

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  {L : Language} [L.Structure k] {P : Set k} (F : OrderedFieldTerms L)
  (hF : InterpretsOrderedFieldTerms (A := k) F)

include hF
omit [IsStrictOrderedRing k] in
private theorem definable_quotient {I : Type*} {f g : (I → k) → k}
    (hf : P.DefinableFun L f) (hg : P.DefinableFun L g) :
    P.DefinableFun L (fun a => f a / g a) := by
  have invMap : P.DefinableMap L (fun a (_ : Fin 1) => g a) := fun _ => hg
  have inv := (F.inv.definableFun_realize.of_empty (A := P)).comp invMap
  have mult : P.DefinableMap L (fun a => ![f a,(g a)⁻¹]) := by
    intro j
    fin_cases j
    · exact hf
    · simpa [hF.inv] using inv
  simpa [hF.mul,div_eq_mul_inv] using (F.mul.definableFun_realize.of_empty (A := P)).comp mult

private theorem definable_within {I : Type*} {f g r : (I → k) → k}
    (hf : P.DefinableFun L f) (hg : P.DefinableFun L g) (hr : P.DefinableFun L r) :
    P.Definable L {a | |f a - g a| < r a} := by
  have left := definable_lt_of_definableFunctions F hF (definable_sub_of_definableFunctions F hF hg hf) hr
  have right := definable_lt_of_definableFunctions F hF (definable_sub_of_definableFunctions F hF hf hg) hr
  convert left.inter right using 1
  ext a
  change |f a - g a| < r a ↔ g a - f a < r a ∧ f a - g a < r a
  rw [abs_lt,← neg_sub,neg_lt_neg_iff]

omit [IsStrictOrderedRing k] in
private theorem definable_positive_quantifier {I : Type*} {Q : (I → k) → k → Prop}
    (hd : P.Definable L {u : I ⊕ Unit → k | Q (u ∘ Sum.inl) (u (.inr ()))})
    (all : Bool) :
    P.Definable L {a | if all then ∀ t > 0, Q a t else ∃ t > 0, Q a t} := by
  have pos : P.Definable L {u : I ⊕ Unit → k | 0 < u (.inr ())} :=
    definable_lt_of_definableFunctions F hF (definable_const_of_closed_term F.zero 0 hF.zero) (DefinableFun.proj L)
  cases all
  · have h := (pos.inter hd).exists_of_finite
    convert h using 1
    ext v
    change (∃ y > 0, Q v y) ↔ ∃ w : Unit → k, 0 < w () ∧ Q v (w ())
    exact ⟨fun ⟨y,hy,hq⟩ => ⟨fun _ => y,hy,hq⟩,fun ⟨w,hy,hq⟩ => ⟨w (),hy,hq⟩⟩
  · apply definable_forall_scalar (P := fun a t => 0 < t → Q a t)
    convert pos.compl.union hd using 1
    ext u
    exact imp_iff_not_or

/-- The derivative of a definable family is a fixed-base definable
relation, in the language of its ordered field. All three quantifiers
in the secant test range over field elements. This also applies to the
ordered residue field on a normalized slice in 3.31. -/
theorem definable_order_derivative_family {I : Type*} [Finite I]
    (G : (I → k) → k → k)
    (hG : P.DefinableFun L (fun a : I ⊕ Unit → k => G (a ∘ Sum.inl) (a (.inr ())))) :
    P.Definable L {w : I ⊕ Fin 2 → k |
      HasOrderDerivativeAt (G (w ∘ Sum.inl)) (w (.inr 0)) (w (.inr 1))} := by
  let B := I ⊕ Fin 2
  let E := B ⊕ Unit
  let D := E ⊕ Unit
  let W := D ⊕ Unit
  let x : W := .inl (.inl (.inl (.inr 0)))
  let m : W := .inl (.inl (.inl (.inr 1)))
  let e : W := .inl (.inl (.inr ()))
  let d : W := .inl (.inr ())
  let y : W := .inr ()
  let pars (i : I) : W := .inl (.inl (.inl (.inl i)))
  let funAt (j : W) (v : W → k) := G (v ∘ pars) (v j)
  have defAt (j : W) : P.DefinableFun L (funAt j) := by
    let ρ := Sum.elim pars (fun _ : Unit => j)
    exact hG.comp (g := fun v => v ∘ ρ) (fun _ => DefinableFun.proj L)
  let q (v : W → k) := (funAt y v - funAt x v)/(v y-v x)
  have dq : P.DefinableFun L q := definable_quotient F hF
    (definable_sub_of_definableFunctions F hF (defAt y) (defAt x))
    (definable_sub_of_definableFunctions F hF (DefinableFun.proj L) (DefinableFun.proj L))
  have ne : P.Definable L {v : W → k | v y ≠ v x} := by
    refine ⟨((Term.var y : (L[[P]]).Term W).equal (.var x)).not,?_⟩
    ext; simp
  have near : P.Definable L {v : W → k | |v y-v x| < v d} :=
    definable_within F hF (DefinableFun.proj L) (DefinableFun.proj L) (DefinableFun.proj L)
  have close : P.Definable L {v : W → k | |q v-v m| < v e} :=
    definable_within F hF dq (DefinableFun.proj L) (DefinableFun.proj L)
  let test (w : B → k) (eps del z : k) := z ≠ w (.inr 0) ∧ |z-w (.inr 0)| < del →
    |(G (w ∘ Sum.inl) z - G (w ∘ Sum.inl) (w (.inr 0))) / (z-w (.inr 0)) - w (.inr 1)| < eps
  have allY : P.Definable L {v : D → k | ∀ z, test ((v ∘ Sum.inl) ∘ Sum.inl)
      (v (.inl (.inr ()))) (v (.inr ())) z} := by
    apply definable_forall_scalar
    convert (ne.inter near).compl.union close using 1
    ext v
    exact imp_iff_not_or
  have someD := definable_positive_quantifier F hF (Q := fun v del =>
    ∀ z, test (v ∘ Sum.inl) (v (.inr ())) del z) allY false
  have allE := definable_positive_quantifier F hF (Q := fun v eps =>
    ∃ del > 0, ∀ z, test v eps del z) someD true
  convert allE using 1
  ext v
  change HasOrderDerivativeAt _ _ _ ↔ ∀ eps > 0, ∃ del > 0, ∀ z, test v eps del z
  constructor
  · intro h eps he
    obtain ⟨del,hd,hlim⟩ := h eps he
    refine ⟨del,hd,fun z ⟨hne,hnear⟩ => ?_⟩
    simpa [test] using hlim (z-v (.inr 0)) (sub_ne_zero.mpr hne) hnear
  · intro h eps he
    obtain ⟨del,hd,hlim⟩ := h eps he
    refine ⟨del,hd,fun t ht hsmall => ?_⟩
    simpa [test] using hlim (v (.inr 0)+t) ⟨by simpa using ht,by simpa using hsmall⟩

end GeneralizedEuler.Section3
