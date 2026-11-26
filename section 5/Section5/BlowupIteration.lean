module

public import Mathlib.Logic.Relation

/-! The exact lengths in the blowup grid and their use in the
common-refinement equivalence. -/

public section

namespace GeneralizedEuler.Section5

variable {X : Type*} (step : X → X → Prop)

/-- A chain of exactly the specified number of forward steps. -/
@[expose] def BlowupSteps : Nat → X → X → Prop
  | 0, a, b => a = b
  | n + 1, a, b => ∃ c, step a c ∧ BlowupSteps n c b

theorem blowupSteps_trans {a b c : X} {m n : Nat}
    (h : BlowupSteps step m a b) (g : BlowupSteps step n b c) :
    BlowupSteps step (m + n) a c := by
  induction m generalizing a with
  | zero =>
    have he : a = b := h
    subst a
    simpa only [Nat.zero_add] using g
  | succ m ih =>
    obtain ⟨x,hx,tail⟩ := h
    rw [Nat.succ_add]
    exact ⟨x,hx,ih tail⟩

variable (diamond : ∀ {a b c}, step a b → step a c → ∃ d, step b d ∧ step c d)

include diamond in
private theorem blowup_strip {a b c : X} {n : Nat}
    (h : step a b) (g : BlowupSteps step n a c) :
    ∃ d, BlowupSteps step n b d ∧ step c d := by
  induction n generalizing a b with
  | zero =>
    have he : a = c := g
    subst c
    exact ⟨b,rfl,h⟩
  | succ n ih =>
    obtain ⟨x,hx,tail⟩ := g
    obtain ⟨y,hby,hxy⟩ := diamond h hx
    obtain ⟨z,hyz,hcz⟩ := ih hxy tail
    exact ⟨z,⟨y,hby,hyz⟩,hcz⟩

include diamond in
/-- A one-step diamond gives the exact complementary lengths of Lemma
5.29. Empty blowup loci are allowed as individual steps. -/
theorem blowup_exact_grid {a b c : X} {m n : Nat}
    (h : BlowupSteps step m a b) (g : BlowupSteps step n a c) :
    ∃ d, BlowupSteps step n b d ∧ BlowupSteps step m c d := by
  induction m generalizing a c with
  | zero =>
    have he : a = b := h
    subst b
    exact ⟨c,g,rfl⟩
  | succ m ih =>
    obtain ⟨x,hx,tail⟩ := h
    obtain ⟨y,hxy,hcy⟩ := blowup_strip step diamond hx g
    obtain ⟨z,hbz,hyz⟩ := ih tail hxy
    exact ⟨z,hbz,⟨y,hcy,hyz⟩⟩

/-- Two objects have a common blowup if their forward chains meet. -/
@[expose] def CommonBlowup (a b : X) : Prop :=
  ∃ c m n, BlowupSteps step m a c ∧ BlowupSteps step n b c

include diamond in
theorem commonBlowup_equivalence : Equivalence (CommonBlowup step) where
  refl _ := ⟨_,0,0,rfl,rfl⟩
  symm := by
    rintro _ _ ⟨c,m,n,h,g⟩
    exact ⟨c,n,m,g,h⟩
  trans := by
    rintro a b c ⟨d,m,n,had,hbd⟩ ⟨e,i,j,hbe,hce⟩
    obtain ⟨f,hdf,hef⟩ := blowup_exact_grid step diamond hbd hbe
    exact ⟨f,m+i,j+n,blowupSteps_trans step had hdf,blowupSteps_trans step hce hef⟩

end GeneralizedEuler.Section5
