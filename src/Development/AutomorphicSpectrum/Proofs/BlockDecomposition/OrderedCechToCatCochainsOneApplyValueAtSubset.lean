import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JBConjTranspose

section
noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed GlobalTheory.CompanionTheory.GLK
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.GLK.Pair

section Ring

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem brk_ee (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r - Complex.I • s))
      - ((1 / 2 : ℂ) • (r - Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q))
      = (1 / 2 : ℂ) • (P - Complex.I • Q) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  linear_combination (norm := skip) (-(Complex.I / 4)) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ff (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p + Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      - ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p + Complex.I • q))
      = (1 / 2 : ℂ) • (P + Complex.I • Q) := by
  subst h1 h2
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ef (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      = ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q)) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (1 / 4 : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

end Ring

section Main

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def eP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z - Complex.I • D (Complex.I • Z))

def fP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z + Complex.I • D (Complex.I • Z))

theorem first_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : e1 D a b = eP D (Matrix.single a b 1) := by
  simp [e1, eP, Matrix.smul_single]

theorem second_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : f1 D a b = fP D (Matrix.single a b 1) := by
  simp [f1, fP, Matrix.smul_single]

variable {D : Mat n → Module.End ℂ V}

theorem D_neg (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (X : Mat n) : D (-X) = -D X := by
  simpa using hs (-1) X

theorem D_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : D (0 : Mat n) = 0 := by
  simpa using hs 0 0

theorem D_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : D (X - Y) = D X - D Y := by
  rw [sub_eq_add_neg, ha, D_neg hs, sub_eq_add_neg]

theorem eP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : eP D (0 : Mat n) = 0 := by
  simp [eP, D_zero hs]

theorem fP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : fP D (0 : Mat n) = 0 := by
  simp [fP, D_zero hs]

theorem eP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : eP D (X - Y) = eP D X - eP D Y := by
  simp only [eP, smul_sub, D_sub ha hs]
  abel

theorem fP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : fP D (X - Y) = fP D X - fP D Y := by
  simp only [fP, smul_sub, smul_add, D_sub ha hs]
  abel

theorem brk_four (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    D Z * D W - D W * D Z = D (Z * W - W * Z) ∧
    D (Complex.I • Z) * D W - D W * D (Complex.I • Z) = D (Complex.I • (Z * W - W * Z)) ∧
    D Z * D (Complex.I • W) - D (Complex.I • W) * D Z = D (Complex.I • (Z * W - W * Z)) ∧
    D (Complex.I • Z) * D (Complex.I • W) - D (Complex.I • W) * D (Complex.I • Z) = -D (Z * W - W * Z) := by
  refine ⟨(hb Z W).symm, ?_, ?_, ?_⟩
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb, ← D_neg hs]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel

theorem eP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * eP D W - eP D W * eP D Z = eP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ee _ _ _ _ _ _ h1 h2 h3 h4

theorem fP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    fP D Z * fP D W - fP D W * fP D Z = fP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ff _ _ _ _ _ _ h1 h2 h3 h4

theorem eP_fP_comm (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * fP D W = fP D W * eP D Z := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ef _ _ _ _ _ _ h1 h2 h3 h4

theorem single_brk (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 - Matrix.single c d (1 : ℂ) * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  have h : ∀ a b c d : Fin n, (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
    intro a b c d
    split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne a b c h 1 (c := (1 : ℂ))
  rw [h, h]

theorem eP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    e1 D a b * e1 D c d - e1 D c d * e1 D a b =
      (if b = c then e1 D a d else 0) - (if d = a then e1 D c b else 0) := by
  simp only [first_generator_eq_single]
  rw [eP_brk hs hb, single_brk, eP_sub ha hs]
  split_ifs <;> simp [eP_zero hs]

theorem fP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    f1 D a b * f1 D c d - f1 D c d * f1 D a b =
      (if b = c then f1 D a d else 0) - (if d = a then f1 D c b else 0) := by
  simp only [second_generator_eq_single]
  rw [fP_brk hs hb, single_brk, fP_sub ha hs]
  split_ifs <;> simp [fP_zero hs]

end Main

theorem gl_pair : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V),
    (∀ X Y, D (X + Y) = D X + D Y) → (∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) →
    (∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) →
    Formalism.REAL.GlRel (e1 D) ∧ Formalism.REAL.GlRel (e2 D) ∧ ∀ a b c d, e1 D a b * e2 D c d = e2 D c d * e1 D a b := by
  intro n V _ _ D ha hs hb
  refine ⟨fun a b c d => eP_units ha hs hb a b c d, fun a b c d => ?_, fun a b c d => ?_⟩
  · have h := fP_units ha hs hb b a d c
    simp only [e2, neg_mul_neg]
    rw [h]
    simp only [eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
    split_ifs <;> simp <;> abel
  · simp only [e2, mul_neg, neg_mul, first_generator_eq_single, second_generator_eq_single]
    rw [eP_fP_comm hs hb]

end GlobalTheory.CompanionTheory.GLK.Pair

end
end

section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

def SmF (n : ℕ) : Submodule ℂ (Mat n → ℂ) where
  carrier := {h | ContDiffOn ℝ ∞ h (GLs n) ∧ ∀ g, g ∉ GLs n → h g = 0}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g hg => by simp [ha.2 g hg, hb.2 g hg]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' c a ha := ⟨contDiffOn_const.smul ha.1, fun g hg => by simp [ha.2 g hg]⟩

theorem indicator_Rd_mem (X : Mat n) (h : SmF n) : (GLs n).indicator (Rd X h.1) ∈ SmF n := by
  refine ⟨(GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X h.2.1).congr fun g hg => Set.indicator_of_mem hg _,
    fun g hg => Set.indicator_of_notMem hg _⟩

def DR (X : Mat n) : Module.End ℂ (SmF n) where
  toFun h := ⟨(GLs n).indicator (Rd X h.1), indicator_Rd_mem X h⟩
  map_add' a b := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      have db := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth b.2.1 hg
      simp only [Submodule.coe_add, Pi.add_apply, Set.indicator_of_mem hg, Rd]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_add_apply' da db _
    · simp [Set.indicator_of_notMem hg]
  map_smul' c a := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      simp only [Submodule.coe_smul, Pi.smul_apply, Set.indicator_of_mem hg, Rd, RingHom.id_apply, smul_eq_mul]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply da c _
    · simp [Set.indicator_of_notMem hg]

def Kf (a b : Fin n) : Module.End ℂ (SmF n) := e1 DR a b + e2 DR a b

def ev1 : SmF n →ₗ[ℂ] ℂ where
  toFun h := h.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Pb (lev : Fin n → ℕ) : Set (Mat n) := {p | p ∈ GLs n ∧ ∀ a b, lev a < lev b → p a b = 0}

def Eqv (lev : Fin n → ℕ) (φ : Mat n → ℂ) : Submodule ℂ (SmF n) where
  carrier := {h | ∀ p ∈ Pb lev, ∀ g ∈ GLs n, h.1 (p * g) = φ p * h.1 g}
  add_mem' {a b} ha hb p hp g hg := by
    simp only [Submodule.coe_add, Pi.add_apply, ha p hp g hg, hb p hp g hg, mul_add]
  zero_mem' p _ g _ := by simp
  smul_mem' c a ha p hp g hg := by
    simp only [Submodule.coe_smul, Pi.smul_apply, ha p hp g hg, smul_eq_mul]
    ring

def muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a =>
  2 * lam a + ((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ)

def yZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a => lam a - muZ lam lev a

def dif (v : Fin n → ℤ) (j : Fin n) : ℤ := v j - if h : (j : ℕ) + 1 < n then v ⟨j + 1, h⟩ else 0

def ini (j : Fin n) : Fin (j + 1) → Fin n := Fin.castLE j.isLt

def lm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) (ini j)).det

def gm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ).det

def fRaw (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Mat n → ℂ :=
  (GLs n).indicator fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j

def cyc (f : SmF n) : Submodule ℂ (SmF n) :=
  (Algebra.adjoin ℂ {T : Module.End ℂ (SmF n) | ∃ a b, T = e1 DR a b ∨ T = e2 DR a b}).toSubmodule.map
    (LinearMap.applyₗ f)

theorem unit_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n :=
  (Matrix.UnitaryGroup.det_isUnit k).ne_zero

theorem DR_apply (X : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (DR X h).1 g = Rd X h.1 g :=
  Set.indicator_of_mem hg _

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (e1 DR a b h).1 g = Eu true a b h.1 g := by
  simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, DR_apply _ _ hg, Eu, Pi.add_apply, if_true, smul_eq_mul]
  ring

theorem liftOneFormsToCompatible_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (f1 DR a b h).1 g = Eu false a b h.1 g := by
  simp [f1, DR_apply _ _ hg, Eu]
  ring

section K

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]

def ipK (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) (x y : SmF n) : ℂ := ∫ k, conj (x.1 k.1) * y.1 k.1 ∂κ

end K

end GlobalTheory.CompanionTheory.ModelS
end
end
