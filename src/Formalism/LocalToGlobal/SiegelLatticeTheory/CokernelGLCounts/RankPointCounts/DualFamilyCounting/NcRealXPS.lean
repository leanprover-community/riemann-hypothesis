import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXSig
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdExactHolds

section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

def sq2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem sq2_mul_sq2_eq_half : sq2 * sq2 = 1 / 2 := by
  unfold sq2
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

theorem star_sq2_eq_self : star sq2 = sq2 := by
  unfold sq2; rw [Complex.star_def, Complex.conj_ofReal]

def u1 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then -sq2 else 1

def u2 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then sq2 else 0

def Pu (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  (if j = i then u1 k r i else 0) + (if i = sig k r j then u2 k r i else 0)

theorem Pu_star (k r : ℕ) (i j : Fin (2 * r + k + 1)) : star (Pu k r i j) = Pu k r i j := by
  unfold Pu u1 u2
  split_ifs <;> simp [star_sq2_eq_self]

theorem PuJPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r) i j = Hpk k r i j := by
  have hJ : Formalism.REAL.Jm (epsK k r) = diagonal (dK k r) := rfl
  rw [hJ, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Hpk_eq]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      rw [if_neg h1, if_neg hjs, if_neg h2', if_neg h3, if_neg hjs]
      norm_num

theorem PuPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Pu k r) i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
  rw [mul_apply, one_apply]
  simp only [conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      simp [h1, hjs, h2', h3]

theorem PuJPu (k r : ℕ) : (Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r = Hpk k r := by
  ext i j; exact PuJPu_apply k r i j

theorem PuPu (k r : ℕ) : (Pu k r)ᴴ * Pu k r = 1 := by
  ext i j; exact PuPu_apply k r i j

theorem exists_unitary {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool)
    (hs : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r ∧ Pᴴ * P = 1 := by
  obtain ⟨σ, hσ⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.PF.exists_perm ε hs
  refine ⟨Matrix.of fun i j => Pu k r (σ.symm i) j, ?_, ?_⟩
  · rw [← PuJPu k r]
    ext a b
    rw [mul_apply, mul_apply]
    simp only [Formalism.REAL.Jm, mul_diagonal, conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply, hσ m]
  · rw [← PuPu k r]
    ext a b
    rw [mul_apply, mul_apply]
    simp only [conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.MainNotions.S

section Coords

variable {m : ℕ}

def realifyE (X : Matrix (Fin m) (Fin m) ℂ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  (WithLp.equiv 2 _).symm (realifyFun X)

theorem realifyE_apply (X : Matrix (Fin m) (Fin m) ℂ) (p : Fin m × Fin m × Bool) :
    (realifyE X).ofLp p = realifyFun X p := rfl

theorem unrealify_realifyE (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (realifyE X) = X := by
  funext i j
  apply Complex.ext
  · first | rfl | simp [unrealify, realifyE, realifyFun]
  · first | rfl | simp [unrealify, realifyE, realifyFun]

theorem realifyE_unrealify (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : realifyE (unrealify x) = x := by
  refine PiLp.ext fun p => ?_
  obtain ⟨i, j, b⟩ := p
  cases b
  · first | rfl | simp [unrealify, realifyE, realifyFun]
  · first | rfl | simp [unrealify, realifyE, realifyFun]

theorem realifyE_add (X Y : Matrix (Fin m) (Fin m) ℂ) : realifyE (X + Y) = realifyE X + realifyE Y := by
  refine PiLp.ext fun p => ?_
  obtain ⟨i, j, b⟩ := p
  cases b <;> simp [realifyE, realifyFun]

theorem realifyE_smul (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : realifyE (c • X) = c • realifyE X := by
  refine PiLp.ext fun p => ?_
  obtain ⟨i, j, b⟩ := p
  cases b <;> simp [realifyE, realifyFun]

theorem unrealify_add (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  rw [← realifyE_unrealify x, ← realifyE_unrealify y, ← realifyE_add, unrealify_realifyE, unrealify_realifyE,
    unrealify_realifyE]

theorem unrealify_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = c • unrealify x := by
  rw [← realifyE_unrealify x, ← realifyE_smul, unrealify_realifyE, unrealify_realifyE]

def adE (A B : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := realifyE (A * unrealify x * B)
  map_add' x y := by simp only [unrealify_add, Matrix.mul_add, Matrix.add_mul, realifyE_add]
  map_smul' c x := by
    simp only [unrealify_smul, Matrix.mul_smul, Matrix.smul_mul, realifyE_smul, RingHom.id_apply]

theorem unrealify_adE (A B : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (adE A B x) = A * unrealify x * B := unrealify_realifyE _

theorem norm_sq_realifyE (Y : Matrix (Fin m) (Fin m) ℂ) : ‖realifyE Y‖ ^ 2 = (trace (Yᴴ * Y)).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [realifyE_apply, realifyFun, if_true, Bool.false_eq_true, if_false, Real.norm_eq_abs, sq_abs,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_adE {P : Matrix (Fin m) (Fin m) ℂ} (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : ‖adE Pᴴ P x‖ = ‖x‖ := by
  have hsq : ‖adE Pᴴ P x‖ ^ 2 = ‖x‖ ^ 2 := by
    show ‖realifyE (Pᴴ * unrealify x * P)‖ ^ 2 = ‖x‖ ^ 2
    conv_rhs => rw [← realifyE_unrealify x]
    rw [norm_sq_realifyE, norm_sq_realifyE]
    congr 1
    have e : (Pᴴ * unrealify x * P)ᴴ * (Pᴴ * unrealify x * P) = Pᴴ * ((unrealify x)ᴴ * unrealify x) * P := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul]
    rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [← Real.sqrt_sq (norm_nonneg (adE Pᴴ P x)), hsq, Real.sqrt_sq (norm_nonneg x)]

def adLE (P : Matrix (Fin m) (Fin m) ℂ) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun := adE Pᴴ P
  invFun := adE P Pᴴ
  map_add' := (adE Pᴴ P).map_add
  map_smul' := (adE Pᴴ P).map_smul
  left_inv x := by
    show realifyE (P * unrealify (realifyE (Pᴴ * unrealify x * P)) * Pᴴ) = x
    rw [unrealify_realifyE]
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one, realifyE_unrealify]
  right_inv x := by
    show realifyE (Pᴴ * unrealify (realifyE (P * unrealify x * Pᴴ)) * P) = x
    rw [unrealify_realifyE]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc _ Pᴴ P, h1, Matrix.mul_one, realifyE_unrealify]

def adIso (P : Matrix (Fin m) (Fin m) ℂ) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  ⟨adLE P h1 h2, norm_adE h1 h2⟩

end Coords

section Lie

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem PHP (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h2 : P * Pᴴ = 1) :
    P * Hpk k r * Pᴴ = Formalism.REAL.Jm ε := by
  rw [← hPJ]
  simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem conj_UH_iff (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Pᴴ * g * P ∈ UH (Hpk k r) ↔ Formalism.REAL.inUJ ε g := by
  have key : (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Pᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * P := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [← PHP hPJ h2]
    simp only [Matrix.mul_assoc]
  show (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Hpk k r ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [key]
  constructor
  · intro h
    have h' := congrArg (fun M => P * M * Pᴴ) h
    have eL : P * (Pᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * P) * Pᴴ = gᴴ * Formalism.REAL.Jm ε * g := by
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      rw [Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one]
    exact eL.symm.trans (h'.trans (PHP hPJ h2))
  · intro h
    rw [h, hPJ]

theorem isUnit_PH (h1 : Pᴴ * P = 1) : IsUnit Pᴴ :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h1)

theorem inv_PH (h1 : Pᴴ * P = 1) : (Pᴴ)⁻¹ = P := Matrix.inv_eq_right_inv h1

theorem exp_conjP (h1 : Pᴴ * P = 1) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (Pᴴ * X * P) = Pᴴ * NormedSpace.exp X * P := by
  have := Matrix.exp_conj Pᴴ X (isUnit_PH h1)
  rwa [inv_PH h1] at this

theorem lieOf_conj (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Pᴴ * X * P ∈ lieOf (UH (Hpk k r)) ↔ X ∈ lieOf {g | Formalism.REAL.inUJ ε g} := by
  simp only [lieOf, Set.mem_setOf_eq]
  refine forall_congr' fun t => ?_
  rw [show ((t : ℂ) • (Pᴴ * X * P)) = Pᴴ * ((t : ℂ) • X) * P by rw [Matrix.mul_smul, Matrix.smul_mul],
    exp_conjP h1, conj_UH_iff hPJ h1 h2]

theorem map_lieE (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    Submodule.map ((adIso P h1 h2 : _ ≃ₗᵢ[ℝ] _).toLinearEquiv.toLinearMap) (Formalism.MainNotions.S.Gauge.gLie ε) =
      lieE (UH (Hpk k r)) := by
  show Submodule.map _ (Submodule.span ℝ _) = Submodule.span ℝ _
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨Pᴴ * X * P, (lieOf_conj hPJ h1 h2 X).2 hX, ?_⟩
    show realifyE (Pᴴ * X * P) = realifyE (Pᴴ * unrealify (realifyE X) * P)
    rw [unrealify_realifyE]
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨realifyE (P * Y * Pᴴ), ⟨P * Y * Pᴴ, (lieOf_conj hPJ h1 h2 _).1 ?_, rfl⟩, ?_⟩
    · have : Pᴴ * (P * Y * Pᴴ) * P = Y := by
        simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [this]; exact hY
    · show realifyE (Pᴴ * unrealify (realifyE (P * Y * Pᴴ)) * P) = realifyE Y
      rw [unrealify_realifyE]
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]

def lieIso (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) :
    Formalism.MainNotions.S.Gauge.gLie ε ≃ₗᵢ[ℝ] lieE (UH (Hpk k r)) :=
  (LinearIsometryEquiv.submoduleMap (Formalism.MainNotions.S.Gauge.gLie ε) (adIso P h1 h2)).trans
    (LinearIsometryEquiv.ofEq _ _ (map_lieE hPJ h1 h2))

theorem unrealify_lieIso (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1)
    (y : Formalism.MainNotions.S.Gauge.gLie ε) :
    unrealify ((lieIso hPJ h1 h2 y : lieE (UH (Hpk k r))) : EuclideanSpace ℝ _) =
      Pᴴ * unrealify (y : EuclideanSpace ℝ _) * P := by
  show unrealify (adE Pᴴ P (y : EuclideanSpace ℝ _)) = _
  exact unrealify_adE _ _ _

end Lie

section Gauge

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem sigmaFinite_smul' {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  have hfin : ∀ i, (c • μ) (spanningSets μ i) < ⊤ := fun i => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top μ i)
  exact ⟨⟨⟨spanningSets μ, fun _ => trivial, hfin, iUnion_spanningSets μ⟩⟩⟩

theorem isHaarOn_smul {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {ν : Measure (Mt k r)}
    (h : IsHaarOn S ν) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) : IsHaarOn S (c • ν) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨sigmaFinite_smul' ν hc, ?_, ?_, fun s hs => ?_⟩
  · intro h0
    have := congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h0
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero, hc0, false_or] at this
    exact h2 (Measure.measure_univ_eq_zero.1 this)
  · rw [Measure.smul_apply, h3, smul_zero]
  · rw [Measure.map_smul, h4 s hs]

theorem preimage_expBall (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) (ρ : ℝ) :
    cM (ε := ε) Pᴴ P ⁻¹' expBall (UH (Hpk k r)) ρ = Formalism.MainNotions.S.Gauge.expSet ε (Metric.ball 0 ρ) := by
  ext g
  simp only [Set.mem_preimage, expBall, Set.mem_image, Formalism.MainNotions.S.Gauge.expSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, hxe⟩
    set y := (lieIso hPJ h1 h2).symm x
    refine ⟨y, ?_, ?_⟩
    · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hx
    · have hxy : lieIso hPJ h1 h2 y = x := LinearIsometryEquiv.apply_symm_apply _ _
      have hu := unrealify_lieIso hPJ h1 h2 y
      rw [hxy] at hu
      have hg : Pᴴ * uMat g * P = NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) := by
        have : (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) = cM (ε := ε) Pᴴ P g := hxe
        exact (funext fun i => funext fun j => congrFun (congrFun this i) j).symm
      rw [hu, exp_conjP h1] at hg
      have := congrArg (fun M => P * M * Pᴴ) hg
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul] at this
      rw [Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one, Matrix.mul_assoc _ P Pᴴ, h2, Matrix.mul_one] at this
      exact this
  · rintro ⟨y, hy, hye⟩
    refine ⟨lieIso hPJ h1 h2 y, ?_, ?_⟩
    · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hy
    · funext i j
      rw [unrealify_lieIso, exp_conjP h1, ← hye]
      rfl

theorem volume_ball_lie (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r) (h1 : Pᴴ * P = 1) (h2 : P * Pᴴ = 1) (ρ : ℝ) :
    volume (Metric.ball (0 : lieE (UH (Hpk k r))) ρ) = volume (Metric.ball (0 : Formalism.MainNotions.S.Gauge.gLie ε) ρ) := by
  have hp := (lieIso hPJ h1 h2).measurePreserving
  have hpre : (lieIso hPJ h1 h2) ⁻¹' Metric.ball 0 ρ = Metric.ball 0 ρ := by
    ext y; simp only [Set.mem_preimage, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  rw [← hp.measure_preimage measurableSet_ball.nullMeasurableSet, hpre]

theorem muG_conj (t : Formalism.REAL.UJ ε) :
    (Formalism.REAL.muG ε).map (fun g => t⁻¹ * g * t) = Formalism.REAL.muG ε := by
  have e : (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t) = (fun g => g * t) ∘ (fun g => t⁻¹ * g) := rfl
  rw [e, ← Measure.map_map (measurable_mul_const t) (measurable_const_mul t⁻¹), map_mul_left_eq_self,
    map_mul_right_eq_self]

end Gauge

theorem gaugeTr_of {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf z0)
    (hG : Formalism.MainNotions.S.Gauge.GaugeDens ε) :
    IsGaugeOn (UH (Hpk k r))
      (((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map
        (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  obtain ⟨P, hPJ, h1⟩ := exists_unitary ε (sig_of_frame hF)
  have h2 : P * Pᴴ = 1 := mul_eq_one_comm.mp h1
  set c : ℝ≥0∞ := (ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ with hc
  have hgpos := hG.2
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hct : c ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hgpos).ne'

  have hQ := gramQ hF
  have hQiQm := Qi_mul_Qm hF
  have hQmQi := Qm_mul_Qi hF
  have ht : (Qm e f wf z0 * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ) = Formalism.REAL.Jm ε := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    calc P * (Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ)
        = P * ((Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0) * Pᴴ := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hQ, PHP hPJ h2]
  set t : Formalism.REAL.UJ ε := toUJ (Qm e f wf z0 * Pᴴ) ht
  have hut : uMat t = Qm e f wf z0 * Pᴴ := uMat_toUJ _ _
  have hut' : uMat t⁻¹ = P * Qi ε e f wf z0 := by
    have hinv : uMat t⁻¹ * uMat t = 1 := by rw [← uMat_mul, inv_mul_cancel, uMat_one]
    have hr : uMat t * (P * Qi ε e f wf z0) = 1 := by
      rw [hut, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, h1, Matrix.one_mul, hQmQi]
    calc uMat t⁻¹ = uMat t⁻¹ * (uMat t * (P * Qi ε e f wf z0)) := by rw [hr, Matrix.mul_one]
      _ = P * Qi ε e f wf z0 := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hfun : cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) = cM (ε := ε) Pᴴ P ∘ (fun g => t⁻¹ * g * t) := by
    funext g
    show (Qi ε e f wf z0 * uMat g * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      Pᴴ * uMat (t⁻¹ * g * t) * P
    rw [uMat_mul, uMat_mul, hut, hut']
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc _ Pᴴ P, h1, Matrix.mul_one]
  have emb := cM_measEmb (ε := ε) (A := Pᴴ) (B := P) (A' := P) (B' := Pᴴ) h2 h2
  have hmapeq : (c • Formalism.REAL.muG ε).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      (c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P) := by
    have hm : Measurable (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t) := (measurable_const_mul t⁻¹).mul_const t
    rw [hfun, ← Measure.map_map emb.measurable hm, Measure.map_smul, muG_conj]
  rw [hmapeq]
  refine ⟨?_, ?_⟩
  · rw [Measure.map_smul]
    exact isHaarOn_smul (isHaarOn_G (P0 := P) (B0 := Pᴴ) ⟨hPJ, by
      rw [← hPJ]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul,
        Formalism.REAL.Jm_mul_self, Matrix.mul_one]⟩) hc0 hct
  · have hratio : ∀ ρ : ℝ,
        (((c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P)) (expBall (UH (Hpk k r)) ρ)).toReal /
          (volume (Metric.ball (0 : lieE (UH (Hpk k r))) ρ)).toReal =
        (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ := by
      intro ρ
      rw [emb.map_apply, preimage_expBall hPJ h1 h2, volume_ball_lie hPJ h1 h2, Measure.smul_apply, smul_eq_mul,
        ENNReal.toReal_mul, hc, ENNReal.toReal_inv, ENNReal.toReal_ofReal hgpos.le, Formalism.MainNotions.S.Gauge.ratioAt,
        mul_div_assoc]
    have hlim : Tendsto (fun ρ => (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ) (𝓝[>] 0)
        (𝓝 ((Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.gaugeU ε)) := hG.1.const_mul _
    rw [inv_mul_cancel₀ hgpos.ne'] at hlim
    exact hlim.congr fun ρ => (hratio ρ).symm

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj CoordinateScalingProducts

theorem coordW_exact (r k : ℕ) (T T' sc : ℝ) (hk : 1 ≤ k) (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc)
    (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
      ENNReal.ofReal ((2 ^ (r + 1) * nrm r sc * lamW r k sc)⁻¹) *
        ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) := by
  have hlam0 : ∀ a, lam r sc a ≠ 0 := lam_ne hsc
  have hΛ0 : 0 < lamW r k sc := Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (hlam0 a)) _
  have hN0 : 0 < nrm r sc := Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hlam0 a)
  have hpos : 0 < 2 ^ (r + 1) * nrm r sc * lamW r k sc := mul_pos (mul_pos (by positivity) hN0) hΛ0

  have hDl : ∀ l, Continuous fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l := by
    intro l
    by_cases hl : l ≤ r + 1
    · have e : (fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l) = fun c => ∏ i : Fin l, c (Fin.castLE hl i) :=
        funext fun c => dl_diag c l hl
      rw [e]; fun_prop
    · have e : (fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l) = fun _ => 0 :=
        funext fun c => by simp [Dl, hl]
      rw [e]; exact continuous_const
  have hGv : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c) := by
    simp only [Gv]
    exact ((hDl (r + 1)).norm.pow 2).sub (continuous_const.mul ((hDl r).norm.pow 2))
  have hGood : MeasurableSet (GoodLoc (r := r) T T') := by
    have e : GoodLoc (r := r) T T' =
        (⋂ l, {c : Fin (r + 1) → ℂ | c l ≠ 0}) ∩ {c | 0 < Gv T T' (Matrix.diagonal c)} := by
      ext c; simp [GoodLoc]
    rw [e]
    exact ((isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const).inter
      (isOpen_lt continuous_const hGv)).measurableSet

  have hptq : ∀ q : (Fin r → ℂ) × ℂ, Complex.normSq q.2 ≠ T * T' →
      Gi r k T T' F (coordSc r sc q) =
        ENNReal.ofReal (lamW r k sc) * (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q)) := by
    intro q hq
    have hw := wt_cs hk T T' sc q
    have hg := gv_cs T T' sc q
    by_cases hq0 : ∀ a, q.1 a ≠ 0
    · by_cases hz : T * T' < Complex.normSq q.2
      · have hmem : coordSc r sc q ∈ GoodLoc (r := r) T T' := by
          refine ⟨fun l => ?_, ?_⟩
          · refine Fin.lastCases ?_ (fun a => ?_) l
            · rw [coordSc_last]
              intro h0
              rw [h0, map_zero] at hz
              exact absurd hz (not_lt.2 (mul_pos hT hT').le)
            · rw [coordSc_cs]; exact mul_ne_zero (hlam0 a) (hq0 a)
          · rw [hg]
            exact mul_pos (Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (mul_ne_zero (hlam0 a) (hq0 a))) 2)
              (by linarith)
        rw [Gi, Set.indicator_of_mem hmem, hw, Formalism.QuantumDeterminants.bcWeight, if_pos hz.le, ENNReal.ofReal_mul hΛ0.le, mul_assoc]
      · have hlt : Complex.normSq q.2 < T * T' := lt_of_le_of_ne (not_lt.1 hz) hq
        have hnot : coordSc r sc q ∉ GoodLoc (r := r) T T' := by
          rintro ⟨-, hp⟩
          rw [hg] at hp
          exact absurd hp (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos
            (Finset.prod_nonneg fun a _ => by positivity) (sub_neg.2 hlt).le))
        rw [Gi, Set.indicator_apply_eq_zero.2 (fun h => absurd h hnot), Formalism.QuantumDeterminants.bcWeight,
          if_neg (not_le.2 hlt), ENNReal.ofReal_zero, zero_mul, mul_zero]
    · push_neg at hq0
      obtain ⟨a, ha⟩ := hq0
      have hnot : coordSc r sc q ∉ GoodLoc (r := r) T T' := by
        rintro ⟨hne, -⟩
        exact hne a.castSucc (by rw [coordSc_cs, ha, mul_zero])
      have hp : ∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by
          rw [ha, norm_zero]
          exact zero_pow (by have := a.isLt; unfold Formalism.QuantumDeterminants.Mdim; omega))
      have hb : Formalism.QuantumDeterminants.bcWeight k r T T' q = 0 := by
        unfold Formalism.QuantumDeterminants.bcWeight; split_ifs <;> simp [hp]
      rw [Gi, Set.indicator_apply_eq_zero.2 (fun h => absurd h hnot), hb, ENNReal.ofReal_zero, zero_mul, mul_zero]

  have hnull : ∀ᵐ c : Fin (r + 1) → ℂ, Complex.normSq (c (Fin.last r)) ≠ T * T' := by
    have hS : (volume : Measure ℂ) {ζ | Complex.normSq ζ = T * T'} = 0 := by
      refine measure_mono_null (fun ζ hζ => ?_) (Measure.addHaar_sphere volume (0 : ℂ) (Real.sqrt (T * T')))
      simp only [Set.mem_setOf_eq] at hζ
      rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    have h0 : (volume : Measure (Fin (r + 1) → ℂ)) {c | Complex.normSq (c (Fin.last r)) = T * T'} = 0 := by
      exact Measure.pi_eval_preimage_null (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (i := Fin.last r) hS
    exact ae_iff.2 (by simpa using h0)
  have hpt : ∀ᵐ c : Fin (r + 1) → ℂ, Gi r k T T' F c = ENNReal.ofReal (lamW r k sc) *
      (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' ((Phe r sc hsc).symm c)) * F c) := by
    filter_upwards [hnull] with c hc
    have hc' : coordSc r sc ((Phe r sc hsc).symm c) = c := by
      rw [← phe_apply hsc, MeasurableEquiv.apply_symm_apply]
    have h2 : ((Phe r sc hsc).symm c).2 = c (Fin.last r) := by
      conv_rhs => rw [← hc']
      rw [coordSc_last]
    have key := hptq ((Phe r sc hsc).symm c) (by rw [h2]; exact hc)
    rw [hc'] at key
    exact key

  have hL : ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
      ENNReal.ofReal (nrm r sc)⁻¹ * ∫⁻ c : Fin (r + 1) → ℂ,
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' ((Phe r sc hsc).symm c)) * F c := by
    rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_Phe hsc, lintegral_map_equiv]
    refine lintegral_congr fun q => ?_
    rw [MeasurableEquiv.symm_apply_apply, phe_apply]
  rw [hL, show (∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r))) =
      ∫⁻ c, Gi r k T T' F c ∂(dcLoc (r := r)) from (lintegral_indicator hGood _).symm,
    dcLoc_eq, lintegral_smul_measure, smul_eq_mul, lintegral_congr_ae hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (inv_pos.2 hpos).le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem lam_one (r : ℕ) (a : Fin r) : lam r 1 a = 1 := by simp [lam]

theorem nrm_one (r : ℕ) : nrm r 1 = 1 := by simp [nrm, lam_one]

theorem lamW_one (r k : ℕ) : lamW r k 1 = 1 := by simp [lamW, lam_one]

theorem coordinate_weight_lintegral (r k : ℕ) (T T' : ℝ) (hk : 1 ≤ k) (hT : 0 < T) (hT' : 0 < T')
    (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r 1 q) =
      ENNReal.ofReal ((2 ^ (r + 1))⁻¹) *
        ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) := by
  rw [coordW_exact r k T T' 1 hk hT hT' one_pos F, nrm_one, lamW_one, mul_one, mul_one]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

theorem disint_switch {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' sc C : ℝ}
    (hF : FrameLoc ε k e z z' T T') {μS μS' : Measure (Formalism.REAL.UJ ε)}
    (hR : ∀ s ∈ SLoc ε e z, μS.map (fun x => x * s) = μS) (hR' : ∀ s ∈ SLoc ε e z', μS'.map (fun x => x * s) = μS')
    {h0 h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} (hh0 : IsSecLoc ε sc e z z' T T' h0)
    (hh : IsSecLoc ε sc e z z' T T' h) (hD : DisintLoc ε k T T' μS μS' h0 C) : DisintLoc ε k T T' μS μS' h C := by
  intro φ hφ
  rw [hD φ hφ]
  refine setLIntegral_congr_fun (JL.measurableSet_goodLoc r T T') (fun c hc => ?_)
  obtain ⟨s₁, hs₁, s₁', hs₁', hg⟩ :=
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds n r k ε e z z' T T' sc hF c hc (h0 c) (h c) (hh0 c hc) (hh c hc)
  rw [hg, JL.inner_dc μS μS' s₁ s₁' (h0 c) (hR s₁ hs₁) (hR' s₁' hs₁') φ]

theorem jacLocX_of (hJ : JacGauge) : JacLocX := by
  intro k r ε e f wf z0 zB zB' hF hk hz hz' hT hT' hG μH μH' hH hH' a a' ha ha' hma hma' κ hκ h hh
  have emb := embQ hF
  have hFL := frameX_of hF hk hz hz' hT hT'
  have hQinv : (Qm e f wf z0)⁻¹ = Qi ε e f wf z0 := Matrix.inv_eq_left_inv (Qi_mul_Qm hF)
  have hdet : IsUnit (Qm e f wf z0).det := Matrix.isUnit_det_of_left_inverse (Qi_mul_Qm hF)
  have hpsi : JL.psiP (ε := ε) (Qm e f wf z0) = cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) := by
    funext u
    show (fun i j => ((Qm e f wf z0)⁻¹ * uMat u * Qm e f wf z0) i j) =
      (Qi ε e f wf z0 * uMat u * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    rw [hQinv]

  obtain ⟨μsec, hμ⟩ := JL.secWb_holds k r zB zB' hk hz hz' hT hT'
  let μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun ζ =>
    if Tz k r zB * Tz k r zB' < Complex.normSq ζ then μsec ζ else 1
  have hμs : IsSection k r zB zB' μs := by
    refine ⟨fun i j => (hμ.1 i j).congr fun ζ hζ => ?_, fun ζ hζ => ?_⟩
    · have hζ' : Tz k r zB * Tz k r zB' < Complex.normSq ζ := hζ
      simp only [μs, if_pos hζ']
    · simp only [μs, if_pos hζ]
      exact hμ.2 ζ hζ
  have hU : ∀ ζ, (μs ζ)ᴴ * Hb k * μs ζ = Hb k := by
    intro ζ
    by_cases hζ : Tz k r zB * Tz k r zB' < Complex.normSq ζ
    · simp only [μs, if_pos hζ]; exact (hμ.2 ζ hζ).1
    · simp only [μs, if_neg hζ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hMuj : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      Formalism.REAL.inUJ ε (Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹) := fun q hq =>
    JL.inUJ_conj (gramQ hF) hdet (JL.bigMem_holds k r q.1 (μs q.2) hq (hU q.2))

  let h0 : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε := fun c =>
    if hc : ∀ a, (JL.qOf r 1 c).1 a ≠ 0 then JL.ujOf _ (hMuj (JL.qOf r 1 c) hc) else 1
  have hh0q : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      uMat (h0 (JL.coordSc r 1 q)) = Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹ := by
    intro q hq
    have hq' : ∀ a, (JL.qOf r 1 (JL.coordSc r 1 q)).1 a ≠ 0 := by rw [JL.qOf_coordSc r one_pos]; exact hq
    simp only [h0, dif_pos hq', JL.uMat_ujOf, JL.qOf_coordSc r one_pos]
  have hh0 : IsSecLoc ε 1 e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') (Tz k r zB) (Tz k r zB') h0 := by
    intro c hc
    have hq1 : ∀ a, (JL.qOf r 1 c).1 a ≠ 0 := fun a =>
      mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ one_ne_zero)) (hc.1 _)
    have hζ : Tz k r zB * Tz k r zB' < Complex.normSq (JL.qOf r 1 c).2 := by
      have h2 := hc.2
      rw [JL.gv_diag_eq] at h2
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨_, h3⟩ | ⟨h3, _⟩
      · show Tz k r zB * Tz k r zB' < Complex.normSq (c (Fin.last r)); linarith
      · exact absurd h3 (not_lt.2 (sq_nonneg _))
    have he0 := hh0q (JL.qOf r 1 c) hq1
    rw [JL.coordSc_qOf r one_pos] at he0
    show Zhat ε (famSc 1 e (Qm e f wf z0 *ᵥ zB)) (famSc 1 e (Qm e f wf z0 *ᵥ zB')) (uMat (h0 c)) = Matrix.diagonal c
    rw [he0, (JL.zBig r k ε e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') zB zB' (Qm e f wf z0) 1 (gramQ hF) hdet
      (fun a => Qm_e (f := f) (wf := wf) (z0 := z0) a) hz hz' rfl rfl one_pos μs hμs (JL.qOf r 1 c) hq1 hζ).2,
      JL.coordSc_qOf r one_pos]

  have hfin : μH Set.univ ≠ ⊤ := by rw [hma]; exact ENNReal.ofReal_ne_top
  have hfin' : μH' Set.univ ≠ ⊤ := by rw [hma']; exact ENNReal.ofReal_ne_top
  refine disint_switch hFL (fun s hs => rightX_of hF hz hT hH hfin κ hκ s hs)
    (fun s hs => rightX_of hF hz' hT' hH' hfin' κ hκ s hs) hh0 hh ?_
  have hW := measW_of hF hH
  have hW' := measW_of hF hH'
  have hWa : (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a := by
    rw [emb.map_apply, Set.preimage_univ, hma]
  have hWa' : (μH'.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a' := by
    rw [emb.map_apply, Set.preimage_univ, hma']
  have hJG := hJ k r zB zB' hk hz hz' hT hT' _ _ _ (gaugeTr_of hF hG) hW hW' a a' ha ha' hWa hWa' κ hκ μs hμs
  have hS1 := measS_of hF hz hT hH κ hκ
  have hS2 := measS_of hF hz' hT' hH' κ hκ
  intro φ hφ
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  let φh : Mt k r → ℝ≥0∞ := Function.extend Ψ φ 0
  have hφh : Measurable φh := emb.measurable_extend hφ measurable_const
  have hext : ∀ u, φh (Ψ u) = φ u := fun u => emb.injective.extend_apply φ 0 u
  have hgU : 0 < Formalism.MainNotions.S.Gauge.gaugeU ε := hG.2
  have hL : ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) = ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε) *
      ∫⁻ x, φh x ∂(((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map Ψ) := by
    rw [emb.lintegral_map, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hgU).ne' ENNReal.ofReal_ne_top, one_mul]
    simp only [hext]
  rw [hL, hJG φh hφh, ← hS1, ← hS2]
  set F : (Fin (r + 1) → ℂ) → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹)
    ∂(muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)) ∂(muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)) with hF0
  have hpt : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r zB) (Tz k r zB') q) *
      ∫⁻ s, ∫⁻ s', φh (fun i j => (Matrix.of s * bigCell k r q.1 (μs q.2) * (Matrix.of s')⁻¹) i j)
        ∂((muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)).map Ψ)
        ∂((muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map Ψ) =
      ENNReal.ofReal (bcWeight k r (Tz k r zB) (Tz k r zB') q) * F (JL.coordSc r 1 q) := by
    intro q
    by_cases hq : ∀ a, q.1 a ≠ 0
    · congr 1
      rw [emb.lintegral_map]
      refine lintegral_congr fun u => ?_
      rw [emb.lintegral_map]
      refine lintegral_congr fun u' => ?_
      have hw := JL.psiP_mul_B hdet u u' (bigCell k r q.1 (μs q.2)) (h0 (JL.coordSc r 1 q)) (hh0q q hq)
      rw [hpsi] at hw
      rw [hw, hext]
    · push_neg at hq
      obtain ⟨a, ha0⟩ := hq
      rw [JL.bcWeight_zero _ _ q a ha0, ENNReal.ofReal_zero, zero_mul, zero_mul]
  rw [lintegral_congr hpt, JL.coordinate_weight_lintegral r k (Tz k r zB) (Tz k r zB') hk hT hT' F]
  have hK0 := Jac.jacConst_nonneg (k := k) (r := r) hT hT' ha ha' hκ
  have hV1 := Jac.volU_pos (k - 1)
  have hCX : Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) =
      Formalism.MainNotions.S.Gauge.gaugeU ε * (jacConst k r (Tz k r zB) (Tz k r zB') a a' κ * (2 ^ (r + 1))⁻¹) := by
    unfold jacConst
    field_simp
  have hC0 : 0 ≤ Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) := by
    rw [hCX]; positivity
  have hpt2 : ∀ c, ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) * wtLoc k (Tz k r zB) (Tz k r zB') c) *
        F c =
      ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2)) *
        (ENNReal.ofReal (wtLoc k (Tz k r zB) (Tz k r zB') c) * F c) := fun c => by
    rw [ENNReal.ofReal_mul hC0, mul_assoc]
  rw [lintegral_congr hpt2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hCX,
    ENNReal.ofReal_mul hgU.le, ENNReal.ofReal_mul hK0]
  ring

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

theorem inN_indep {n r : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ}
    (hz' : ∀ a, hJ ε (e a) z' = 0) {g : Matrix (Fin n) (Fin n) ℂ} (h : InN ε e z g) : InN ε e z' g :=
  ⟨⟨h.1.1, h.2 z' hz'⟩, h.2⟩

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem Qm_mulVec_eq_sum (w : Fin (2 * r + k + 1) → ℂ) : Qm e f wf z0 *ᵥ w = ∑ j, w j • colQ e f wf z0 j := by
  funext i
  simp only [mulVec, dotProduct, Qm, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem Qm_mem_spanLt {a : ℕ} (ha : a ≤ r) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → w i = 0) : Qm e f wf z0 *ᵥ w ∈ spanLt e a := by
  rw [Qm_mulVec_eq_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases hj : j.val < a
  · have hjr : j.val < r := lt_of_lt_of_le hj ha
    have hc : colQ e f wf z0 j = e ⟨j.val, hjr⟩ := by simp [colQ, hjr]
    rw [hc]
    unfold spanLt
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j.val, hjr⟩, hj, rfl⟩)
  · rw [hw j (not_lt.mp hj), zero_smul]
    exact Submodule.zero_mem _

theorem sub_one_eI {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) (a : Fin r)
    (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) : ((m - 1) *ᵥ bvec (eI k r a)) i = 0 := by
  rw [bvec, mulVec_single_one, col_apply, Matrix.sub_apply, hm.2.1 a i hi, one_apply, sub_self]

theorem sub_one_mulVec_apply_eq_zero_of_mem_Nset {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r)
    (w : Fin (2 * r + k + 1) → ℂ) (hw : ∀ j : Fin (2 * r + k + 1), r + k < j.val → w j = 0)
    (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : ((m - 1) *ᵥ w) i = 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases lt_or_ge (r + k) j.val with hj | hj
  · rw [hw j hj, mul_zero]
  · rcases lt_or_ge j.val r with hj' | hj'
    · have h1 := hm.2.1 ⟨j.val, hj'⟩ i (by show j.val ≤ i.val; omega)
      have he : eI k r ⟨j.val, hj'⟩ = j := Fin.ext rfl
      rw [he] at h1
      rw [Matrix.sub_apply, h1, one_apply, sub_self, zero_mul]
    · rw [Matrix.sub_apply, hm.2.2 i j hj' hj hi, one_apply, sub_self, zero_mul]

theorem Qi_perp (y : Fin (2 * r + k + 1) → ℂ) (hy : ∀ a, hJ ε (e a) y = 0) (j : Fin (2 * r + k + 1))
    (hj : r + k < j.val) : (Qi ε e f wf z0 *ᵥ y) j = 0 := by
  have hv : ∀ l : Fin (2 * r + k + 1), l.val < r → ((Qm e f wf z0)ᴴ *ᵥ (REAL.Jm ε *ᵥ y)) l = 0 := by
    intro l hl
    have hc : colQ e f wf z0 l = e ⟨l.val, hl⟩ := by simp [colQ, hl]
    have h1 := hy ⟨l.val, hl⟩
    rw [← hc] at h1
    rw [← h1]
    simp only [hJ, mulVec, dotProduct, conjTranspose_apply, Qm, of_apply, Pi.star_apply]
  unfold Qi
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  change ∑ l, Hpk k r j l * ((Qm e f wf z0)ᴴ *ᵥ (REAL.Jm ε *ᵥ y)) l = 0
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < r
  · rw [hv l hl, mul_zero]
  · have h0 : Hpk k r j l = 0 := by
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> first | rfl | omega
    rw [h0, zero_mul]

theorem inN_of_conj (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hzB : inWb k r zB)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : Qi ε e f wf z0 * g * Qm e f wf z0 ∈ Nset k r) :
    InN ε e (Qm e f wf z0 *ᵥ zB) g := by
  have hg : Qm e f wf z0 * (Qi ε e f wf z0 * g * Qm e f wf z0) * Qi ε e f wf z0 = g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul, Matrix.mul_assoc,
      Qm_mul_Qi hF, Matrix.mul_one]
  have key : ∀ v, (g - 1) *ᵥ v
      = Qm e f wf z0 *ᵥ ((Qi ε e f wf z0 * g * Qm e f wf z0 - 1) *ᵥ (Qi ε e f wf z0 *ᵥ v)) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, hg, Matrix.mul_one, Qm_mul_Qi hF]
  have hz : Qi ε e f wf z0 *ᵥ (Qm e f wf z0 *ᵥ zB) = zB := by
    rw [mulVec_mulVec, Qi_mul_Qm hF, one_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, Qi_e hF]
    exact Qm_mem_spanLt (le_of_lt a.isLt) _ (fun i hi => sub_one_eI hm a i hi)
  · rw [key, hz]
    exact Qm_mem_spanLt le_rfl _ (fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Nset hm zB (fun j hj => hzB j (Or.inr hj)) i hi)
  · rw [key]
    exact Qm_mem_spanLt le_rfl _ (fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Nset hm _ (fun j hj => Qi_perp y hy j hj) i hi)

theorem refN_map (hF : IsFrameJ ε e f wf z0) :
    (refN ε e f wf z0).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) = Jac.N1 k r := by
  have h := measN_of hF 1
  rwa [ENNReal.ofReal_one, one_smul] at h

theorem refN_isHaarLoc (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hzB : inWb k r zB)
    (hz0 : ∃ t : ℂ, z0 = t • (Qm e f wf z0 *ᵥ zB)) :
    IsHaarLoc (NLoc ε e (Qm e f wf z0 *ᵥ zB)) (refN ε e f wf z0) := by
  set C := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hC
  have hE : MeasurableEmbedding C := embQ hF
  have hmap : Measure.map C (refN ε e f wf z0) = Jac.N1 k r := refN_map hF
  have hH := Jac.nilradical_measure_is_haar (k := k) (r := r)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : SigmaFinite (Measure.map C (refN ε e f wf z0)) := by
      rw [hmap]
      exact hH.1
    exact SigmaFinite.of_map _ hE.measurable.aemeasurable hs
  · intro h0
    apply hH.2.1
    rw [← hmap, h0, Measure.map_zero]
  · refine measure_mono_null (t := C ⁻¹' {x : Mt k r | of x ∉ Nset k r}) ?_ ?_
    · intro g hg
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      intro hm
      exact hg (inN_of_conj hF hzB hm)
    · rw [← hE.map_apply, hmap]
      exact hH.2.2.1
  · intro s hs
    have hsN := conj_mem_Nset hF hz0 (uMat_mem s) hs
    have hcomp : C ∘ (fun x => s * x) = lmulM (Qi ε e f wf z0 * uMat s * Qm e f wf z0) ∘ C := by
      funext x
      simp only [Function.comp_apply, hC]
      rw [lmulM_cM]
      show Qi ε e f wf z0 * uMat (s * x) * Qm e f wf z0
        = Qi ε e f wf z0 * uMat s * Qm e f wf z0 * Qi ε e f wf z0 * uMat x * Qm e f wf z0
      rw [uMat_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Qm e f wf z0) (Qi ε e f wf z0), Qm_mul_Qi hF, Matrix.one_mul]
    have hms : Measurable (fun x : ↥(REAL.UJ ε) => s * x) := by
      rw [← hE.measurable_comp_iff, hcomp]
      exact (measurable_lmulM _).comp hE.measurable
    have hmm : Measure.map C (Measure.map (fun x => s * x) (refN ε e f wf z0))
        = Measure.map C (refN ε e f wf z0) := by
      rw [Measure.map_map hE.measurable hms, hcomp, ← Measure.map_map (measurable_lmulM _) hE.measurable,
        hmap, hH.2.2.2 _ hsN]
    calc Measure.map (fun x => s * x) (refN ε e f wf z0)
        = Measure.comap C (Measure.map C (Measure.map (fun x => s * x) (refN ε e f wf z0))) :=
          (hE.comap_map _).symm
      _ = Measure.comap C (Measure.map C (refN ε e f wf z0)) := by rw [hmm]
      _ = refN ε e f wf z0 := hE.comap_map _

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

def refNg : {n r k : ℕ} → n = 2 * r + k + 1 → (ε : Fin n → Bool) → (Fin r → Fin n → ℂ) → (Fin r → Fin n → ℂ) →
    (Fin k → Fin n → ℂ) → (Fin n → ℂ) → Measure (Formalism.REAL.UJ ε)
  | _, _, _, rfl, ε, e, f, wf, z0 => refN ε e f wf z0

theorem refNg_rfl {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) :
    refNg rfl ε e f wf z0 = refN ε e f wf z0 := rfl

theorem muSL_smul {n : ℕ} {ε : Fin n → Bool} (μH μN : Measure (Formalism.REAL.UJ ε)) [SFinite μH] (c : ℝ≥0∞) :
    muSL μH (c • μN) = c • muSL μH μN := by
  unfold muSL; rw [Measure.prod_smul_left, Measure.map_smul]

theorem disint_smul_right {n r k : ℕ} {ε : Fin n → Bool} {T T' : ℝ} {μS μS' : Measure (Formalism.REAL.UJ ε)}
    {h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} {C c : ℝ} (hc : 0 < c) (hD : DisintLoc ε k T T' μS μS' h C) :
    DisintLoc ε k T T' μS (ENNReal.ofReal c • μS') h (C / c) := by
  intro φ hφ
  rw [hD φ hφ]
  refine setLIntegral_congr_fun (JL.measurableSet_goodLoc r T T') (fun x _ => ?_)
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul' hc.le]
  congr 2
  field_simp

theorem placeStep (hJG : JacGauge) {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z z' : Fin n → ℂ) {T T' : ℝ} (hk : 1 ≤ k) (hT : 0 < T)
    (hT' : 0 < T') (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0)
    (hez' : ∀ a, hJ ε (e a) z' = 0) (hfz' : ∀ a, hJ ε (f a) z' = 0) (hzz' : hJ ε z' z' = -(T' : ℂ))
    (hG : Formalism.MainNotions.S.Gauge.GaugeDens ε) (μH μH' : Measure (Formalism.REAL.UJ ε))
    (hH : IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) μH) (hH' : IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z') μH')
    (a a' : ℝ) (ha : 0 < a) (ha' : 0 < a') (hma : μH Set.univ = ENNReal.ofReal a)
    (hma' : μH' Set.univ = ENNReal.ofReal a') (κ κ' : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ')
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (hh : IsSecLoc ε 1 e z z' T T' h) :
    DisintLoc ε k T T' (muSL μH (ENNReal.ofReal κ • refNg hn ε e f wf (z0v T z)))
      (muSL μH' (ENNReal.ofReal κ' • refNg hn ε e f wf (z0v T z))) h
      (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
        ((T * T') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * (κ * κ'))) := by
  subst hn
  have hs : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ * T = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hsC : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * (T : ℂ) = 1 := by exact_mod_cast hs
  have hFJ : IsFrameJ ε e f wf (z0v T z) :=
    { ee := hee, ff := hff, ef := hef
      ez := fun a => by rw [z0v, JL.hJ_smul_r, hez, mul_zero]
      fz := fun a => by rw [z0v, JL.hJ_smul_r, hfz, mul_zero]
      zz := by
        rw [z0v, JL.hJ_smul_l, JL.hJ_smul_r, hzz, Complex.conj_ofReal]
        linear_combination (-1 : ℂ) * hsC
      ww := hww, ew := hew, fw := hfw
      zw := fun a => by rw [z0v, JL.hJ_smul_l, hzw, mul_zero] }
  have hzB : inWb k r (zBv k r T) := inWb_zB T
  have hQzB : Qm e f wf (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  have hTzB : Tz k r (zBv k r T) = T := Tz_zB hT.le
  set zB' := Qi ε e f wf (z0v T z) *ᵥ z' with hzB'
  have hQzB' : Qm e f wf (z0v T z) *ᵥ zB' = z' := by
    rw [hzB', Matrix.mulVec_mulVec, Qm_mul_Qi hFJ, Matrix.one_mulVec]
  have hzB'W : inWb k r zB' := by
    intro i hi
    rcases hi with hi | hi
    · have hie : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hie, hzB', Qi_mulVec_eI, hfz']
    · exact Qi_perp z' hez' i hi
  have hTzB' : Tz k r zB' = T' := by
    have hw := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_P (gramQ hFJ) zB' zB'
    rw [hQzB', hzz'] at hw
    unfold Tz
    rw [← hw]
    simp
  have hHB : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf (z0v T z) *ᵥ zBv k r T)) μH := by
    rw [hQzB]; exact hH
  have hHB' : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf (z0v T z) *ᵥ zB')) μH' := by
    rw [hQzB']; exact hH'
  have hhB : IsSecLoc ε 1 e (Qm e f wf (z0v T z) *ᵥ zBv k r T) (Qm e f wf (z0v T z) *ᵥ zB')
      (Tz k r (zBv k r T)) (Tz k r zB') h := by
    rw [hQzB, hQzB', hTzB, hTzB']; exact hh
  have hD := jacLocX_of hJG k r ε e f wf (z0v T z) (zBv k r T) zB' hFJ hk hzB hzB'W (by rw [hTzB]; exact hT)
    (by rw [hTzB']; exact hT') hG μH μH' hHB hHB' a a' ha ha' hma hma' κ hκ h hhB
  rw [hTzB, hTzB'] at hD
  have hD2 := disint_smul_right (c := κ' / κ) (div_pos hκ' hκ) hD
  haveI : SigmaFinite μH' := hH'.1
  have hm : muSL μH' (ENNReal.ofReal κ' • refN ε e f wf (z0v T z)) =
      ENNReal.ofReal (κ' / κ) • muSL μH' (ENNReal.ofReal κ • refN ε e f wf (z0v T z)) := by
    rw [muSL_smul, muSL_smul, smul_smul, ← ENNReal.ofReal_mul (div_pos hκ' hκ).le, div_mul_cancel₀ _ hκ.ne']
  show DisintLoc ε k T T' (muSL μH (ENNReal.ofReal κ • refN ε e f wf (z0v T z)))
    (muSL μH' (ENNReal.ofReal κ' • refN ε e f wf (z0v T z))) h _
  rw [hm]
  convert hD2 using 1
  have hV1 := Jac.volU_pos (k - 1)
  field_simp

theorem refNg_isHaarLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z z' : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) (hez' : ∀ a, hJ ε (e a) z' = 0) :
    IsHaarLoc (NLoc ε e z') (refNg hn ε e f wf (z0v T z)) := by
  subst hn
  have hs : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ * T = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hsC : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * (T : ℂ) = 1 := by exact_mod_cast hs
  have hFJ : IsFrameJ ε e f wf (z0v T z) :=
    { ee := hee, ff := hff, ef := hef
      ez := fun a => by rw [z0v, JL.hJ_smul_r, hez, mul_zero]
      fz := fun a => by rw [z0v, JL.hJ_smul_r, hfz, mul_zero]
      zz := by
        rw [z0v, JL.hJ_smul_l, JL.hJ_smul_r, hzz, Complex.conj_ofReal]
        linear_combination (-1 : ℂ) * hsC
      ww := hww, ew := hew, fw := hfw
      zw := fun a => by rw [z0v, JL.hJ_smul_l, hzw, mul_zero] }
  have hQzB : Qm e f wf (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f wf (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQzB]; rfl⟩
  have h0 := refN_isHaarLoc hFJ (inWb_zB T) hz0
  rw [hQzB] at h0
  obtain ⟨h1, h2, h3, h4⟩ := h0
  have hNeq : NLoc ε e z' = NLoc ε e z := by
    ext g
    exact ⟨fun hg => inN_indep hez hg, fun hg => inN_indep hez' hg⟩
  show IsHaarLoc (NLoc ε e z') (refN ε e f wf (z0v T z))
  rw [hNeq]
  exact ⟨h1, h2, h3, h4⟩

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section
noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem isFrameJ_of {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z : Fin (2 * r + k + 1) → ℂ} {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) : IsFrameJ ε e f wf (z0v T z) := by
  have hl : ∀ (x y : Fin (2 * r + k + 1) → ℂ) (c : ℂ), hJ ε (c • x) y = star c * hJ ε x y := by
    intro x y c
    simp [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul]
  have hr : ∀ (x y : Fin (2 * r + k + 1) → ℂ) (c : ℂ), hJ ε x (c • y) = c * hJ ε x y := by
    intro x y c
    simp [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul]
  have hsc : star ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  have key : ((Real.sqrt T)⁻¹ * ((Real.sqrt T)⁻¹ * -T) : ℝ) = -1 := by
    rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hT.le, mul_neg, inv_mul_cancel₀ hT.ne']
  refine ⟨hee, hff, hef, ?_, ?_, ?_, hww, hew, hfw, ?_⟩
  · intro a
    rw [Formalism.L2.SG.Pf.WFL.z0v, hr, hez, mul_zero]
  · intro a
    rw [Formalism.L2.SG.Pf.WFL.z0v, hr, hfz, mul_zero]
  · rw [Formalism.L2.SG.Pf.WFL.z0v, hl, hr, hzz, hsc]
    exact_mod_cast key
  · intro a
    rw [Formalism.L2.SG.Pf.WFL.z0v, hl, hzw, mul_zero]

theorem hLoc_eq {n r : ℕ} (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    Formalism.L2.SG.Pf.NcReal.HLoc ε e f z = Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc ε e f z := by
  ext s
  simp only [Formalism.L2.SG.Pf.NcReal.HLoc, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc, Set.mem_setOf_eq, forall_and,
    and_assoc]

theorem compact_HLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (wf : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) : IsCompact (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have hemb := cM_closedEmb (ε := ε) (A := Qi ε e f wf (z0v T z)) (B := Qm e f wf (z0v T z))
    (A' := Qm e f wf (z0v T z)) (B' := Qi ε e f wf (z0v T z)) (Qm_mul_Qi hFJ) (Qm_mul_Qi hFJ)
  have hW : IsCompact (UWset k r (zBv k r T) : Set (Mt k r)) :=
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r (zBv k r T) (inWb_zB T) (by rw [Tz_zB hT.le]; exact hT)
  have hK := hemb.isCompact_preimage hW
  have hcl : IsClosed (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) := by
    rw [hLoc_eq]
    exact NilradicalHermitianFrames.NH.HG_closed ε e f z
  refine hK.of_isClosed_subset hcl fun g hg => ?_
  exact conj_mem_UWset hFJ (Qm_zB hT z) (uMat_mem g) (fun a => (hg.1 a).1) (fun a => (hg.1 a).2) hg.2

theorem pi_smul_factors {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  haveI : ∀ i, SigmaFinite (c i • μ i) := fun i =>
    ⟨⟨⟨spanningSets (μ i), fun _ => Set.mem_univ _, fun n => by
        rw [Measure.smul_apply, smul_eq_mul]
        exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top (hc i) (measure_spanningSets_lt_top (μ i) n).ne),
      iUnion_spanningSets (μ i)⟩⟩⟩
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

theorem isHaarLoc_smul {n : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {μ : Measure (Formalism.REAL.UJ ε)}
    (h : IsHaarLoc S μ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) : IsHaarLoc S (c • μ) := by
  unfold Formalism.L2.SG.RealObj.IsHaarLoc at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  haveI := h1
  refine ⟨⟨⟨⟨spanningSets μ, fun _ => Set.mem_univ _, fun n => ?_, iUnion_spanningSets μ⟩⟩⟩, ?_, ?_, ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top hc (measure_spanningSets_lt_top μ n).ne)
  · intro h0
    apply h2
    ext s _
    simpa [hc0] using congrArg (fun m : Measure (Formalism.REAL.UJ ε) => m s) h0
  · simp [h3]
  · intro s hs
    rw [Measure.map_smul, h4 s hs]

end Gen

section HidaSetting

variable {D : D7} (X : HidaSetting D)

theorem nX : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  rw [X.n_eq]
  have hm := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

def refNX (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  refNg (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (z0v (Tw u) (ProductExactness.zV X u v))

section Facts

variable (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)

theorem fX_ee : ∀ a b, hJ (X.B.I.ε v) (eV X v a) (eV X v b) = 0 := fun a b =>
  (ProductExactness.hJ_X X v _ _).trans (by rw [X.ee]; simp)
theorem fX_ff : ∀ a b, hJ (X.B.I.ε v) (ProductExactness.pV X v a) (ProductExactness.pV X v b) = 0 := fun a b =>
  (ProductExactness.hJ_X X v _ _).trans (by rw [X.ff]; simp)
theorem fX_ef : ∀ a b, hJ (X.B.I.ε v) (eV X v a) (ProductExactness.pV X v b) = if a = b then 1 else 0 := fun a b =>
  (ProductExactness.hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
theorem fX_ww : ∀ a b, hJ (X.B.I.ε v) (X.wfr u v a) (X.wfr u v b) = if a = b then 1 else 0 := X.wfr_on u v
theorem fX_ew : ∀ c a, hJ (X.B.I.ε v) (eV X v c) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).1
theorem fX_fw : ∀ c a, hJ (X.B.I.ε v) (ProductExactness.pV X v c) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).2
theorem fX_ez : ∀ a, hJ (X.B.I.ε v) (eV X v a) (ProductExactness.zV X u v) = 0 := (ProductExactness.frameLoc_X X u u v).ez
theorem fX_fz : ∀ a, hJ (X.B.I.ε v) (ProductExactness.pV X v a) (ProductExactness.zV X u v) = 0 := fun a =>
  (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).2]; simp)
theorem frame_real_z_z_eq_neg : hJ (X.B.I.ε v) (ProductExactness.zV X u v) (ProductExactness.zV X u v) = -((Tw u : ℝ) : ℂ) :=
  (ProductExactness.frameLoc_X X u u v).zz
theorem fX_zw : ∀ a, hJ (X.B.I.ε v) (ProductExactness.zV X u v) (X.wfr u v a) = 0 := fun a => (X.wfr_perp u v a).2

end Facts

theorem muNv_eq (u w : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ∃ d : ℝ≥0∞, d ≠ 0 ∧ d ≠ ⊤ ∧ ProductExactness.muNv X w v = d • refNX X u v := by
  have hR := refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
    (ProductExactness.zV X w v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X w v)
  obtain ⟨r1, r2, r3, r4⟩ := hR
  obtain ⟨⟨m1, m2, m3, m4⟩, -⟩ := ProductExactness.muNv_haar X w v
  haveI : SigmaFinite (refNX X u v) := r1
  exact ProductExactness.PiM.uniq_on_closed (ProductExactness.NGv X w v) (NilradicalHermitianFrames.NH.NG_closed _ _ _) _ _ m3 r3 m4 r4 m2 r2

theorem muHv_mass (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ProductExactness.muHv X u v Set.univ ≠ 0 ∧ ProductExactness.muHv X u v Set.univ ≠ ⊤ := by
  obtain ⟨⟨m1, m2, m3, m4⟩, m5⟩ := ProductExactness.muHv_haar X u v
  have hK := compact_HLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
    (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  rw [hLoc_eq] at hK
  refine ⟨fun h0 => m2 (Measure.measure_univ_eq_zero.1 h0), ?_⟩
  have hsplit : ProductExactness.muHv X u v Set.univ ≤
      ProductExactness.muHv X u v (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v)) +
        ProductExactness.muHv X u v (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v))ᶜ := by
    rw [← Set.union_compl_self (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v)
      (ProductExactness.zV X u v))]
    exact measure_union_le _ _
  have m3' : ProductExactness.muHv X u v
      (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v))ᶜ = 0 := m3
  rw [m3', add_zero] at hsplit
  exact (lt_of_le_of_lt hsplit (hK.measure_lt_top)).ne

end HidaSetting

def CovolRef : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' →
      ((Measure.pi (refNX X u)) FdN).toReal * ((Measure.pi (refNX X u)) FdN').toReal =
        |(NumberField.discr X.B.I.F : ℝ)| ^ eDF D.R.k D.R.rS

theorem placeSplit_of (hJG : JacGauge) (hC : CovolRef) : PlaceSplit := by
  classical
  intro D X hb FdN FdN' u u' ψ hHyp _ _ hGd
  obtain ⟨v0⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega

  obtain ⟨κN, hκN0, hκNT, hN⟩ := ProductExactness.muN_eq X u
  obtain ⟨κN', hκN'0, hκN'T, hN'⟩ := ProductExactness.muN_eq X u'
  choose d hd0 hdT hd using fun v => muNv_eq X u u v
  choose d' hd'0 hd'T hd' using fun v => muNv_eq X u u' v
  set cN : InfinitePlace X.B.I.F → ℝ≥0∞ := fun v => (if v = v0 then κN else 1) * d v with hcN
  set cN' : InfinitePlace X.B.I.F → ℝ≥0∞ := fun v => (if v = v0 then κN' else 1) * d' v with hcN'
  have hcT : ∀ v, cN v ≠ ⊤ := fun v => ENNReal.mul_ne_top (by split_ifs <;> simp [hκNT]) (hdT v)
  have hcT' : ∀ v, cN' v ≠ ⊤ := fun v => ENNReal.mul_ne_top (by split_ifs <;> simp [hκN'T]) (hd'T v)
  have hc0 : ∀ v, cN v ≠ 0 := fun v => mul_ne_zero (by split_ifs <;> simp [hκN0]) (hd0 v)
  have hc0' : ∀ v, cN' v ≠ 0 := fun v => mul_ne_zero (by split_ifs <;> simp [hκN'0]) (hd'0 v)
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
      (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X u v)).1
  have hprod : ∀ (κ0 : ℝ≥0∞) (dd : InfinitePlace X.B.I.F → ℝ≥0∞), (∀ v, dd v ≠ ⊤) → κ0 ≠ ⊤ →
      κ0 • Measure.pi (fun v => dd v • refNX X u v) =
        Measure.pi (fun v => ((if v = v0 then κ0 else 1) * dd v) • refNX X u v) := by
    intro κ0 dd hddT hκ0
    rw [pi_smul_factors _ dd hddT, pi_smul_factors _ _ (fun v => ENNReal.mul_ne_top
      (by split_ifs <;> simp [hκ0]) (hddT v)), smul_smul, Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hmuN : X.muN u = Measure.pi (fun v => cN v • refNX X u v) := by
    have he : ProductExactness.muNv X u = fun v => d v • refNX X u v := funext hd
    rw [hN, he]
    exact hprod κN d hdT hκNT
  have hmuN' : X.muN u' = Measure.pi (fun v => cN' v • refNX X u v) := by
    have he : ProductExactness.muNv X u' = fun v => d' v • refNX X u v := funext hd'
    rw [hN', he]
    exact hprod κN' d' hd'T hκN'T

  obtain ⟨κH, hκH0, hκHT, hH⟩ := ProductExactness.muH_eq X u
  obtain ⟨κH', hκH'0, hκH'T, hH'⟩ := ProductExactness.muH_eq X u'
  set μH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (if v = v0 then κH else 1) • ProductExactness.muHv X u v with hμH
  set μH' : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (if v = v0 then κH' else 1) • ProductExactness.muHv X u' v
    with hμH'
  have hsH : ∀ v, (if v = v0 then κH else 1) ≠ 0 ∧ (if v = v0 then κH else 1) ≠ ⊤ := fun v => by
    split_ifs <;> simp [hκH0, hκHT]
  have hsH' : ∀ v, (if v = v0 then κH' else 1) ≠ 0 ∧ (if v = v0 then κH' else 1) ≠ ⊤ := fun v => by
    split_ifs <;> simp [hκH'0, hκH'T]
  have hmuH : X.muH u = Measure.pi μH := by
    have hp : (∏ v, (if v = v0 then κH else 1 : ℝ≥0∞)) = κH := by simp
    rw [hH, hμH, pi_smul_factors _ _ (fun v => (hsH v).2), hp]
  have hmuH' : X.muH u' = Measure.pi μH' := by
    have hp : (∏ v, (if v = v0 then κH' else 1 : ℝ≥0∞)) = κH' := by simp
    rw [hH', hμH', pi_smul_factors _ _ (fun v => (hsH' v).2), hp]
  have hHaarH : ∀ v, IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v)) (μH v) :=
    fun v => by
      rw [hLoc_eq]
      exact isHaarLoc_smul (ProductExactness.muHv_haar X u v).1 (hsH v).1 (hsH v).2
  have hHaarH' : ∀ v, IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u' v))
      (μH' v) := fun v => by
    rw [hLoc_eq]
    exact isHaarLoc_smul (ProductExactness.muHv_haar X u' v).1 (hsH' v).1 (hsH' v).2
  have hmH : ∀ v, μH v Set.univ ≠ 0 ∧ μH v Set.univ ≠ ⊤ := fun v => by
    obtain ⟨h1, h2⟩ := muHv_mass X u v
    simp only [hμH, Measure.smul_apply, smul_eq_mul]
    exact ⟨mul_ne_zero (hsH v).1 h1, ENNReal.mul_ne_top (hsH v).2 h2⟩
  have hmH' : ∀ v, μH' v Set.univ ≠ 0 ∧ μH' v Set.univ ≠ ⊤ := fun v => by
    obtain ⟨h1, h2⟩ := muHv_mass X u' v
    simp only [hμH', Measure.smul_apply, smul_eq_mul]
    exact ⟨mul_ne_zero (hsH' v).1 h1, ENNReal.mul_ne_top (hsH' v).2 h2⟩

  refine ⟨fun v => cN v • refNX X u v, fun v => cN' v • refNX X u v, μH, μH',
    fun v => (μH v Set.univ).toReal, fun v => (μH' v Set.univ).toReal, fun v => (cN v).toReal,
    fun v => (cN' v).toReal, ((Measure.pi (refNX X u)) FdN).toReal, ((Measure.pi (refNX X u)) FdN').toReal,
    fun v => ProductExactness.sf_smul _ _ (hcT v), fun v => ProductExactness.sf_smul _ _ (hcT' v), fun v => (hHaarH v).1,
    fun v => (hHaarH' v).1, fun v => ⟨ENNReal.toReal_pos (hmH v).1 (hmH v).2, ENNReal.toReal_pos (hmH' v).1 (hmH' v).2,
      ENNReal.toReal_pos (hc0 v) (hcT v), ENNReal.toReal_pos (hc0' v) (hcT' v)⟩,
    hmuN, hmuN', hmuH, hmuH', fun v => (ENNReal.ofReal_toReal (hmH v).2).symm,
    fun v => (ENNReal.ofReal_toReal (hmH' v).2).symm, ?_, ?_, ?_, hC X hb FdN FdN' u u' hHyp⟩
  · intro v h hh
    have hP := placeStep hJG (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u' v) hk (ProductExactness.Tw_pos u) (ProductExactness.Tw_pos u') (fX_ee X v) (fX_ff X v) (fX_ef X v)
      (fX_ww X u v) (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
      (fX_ez X u' v) (fX_fz X u' v) (frame_real_z_z_eq_neg X u' v) (hGd v) (μH v) (μH' v) (hHaarH v) (hHaarH' v)
      _ _ (ENNReal.toReal_pos (hmH v).1 (hmH v).2) (ENNReal.toReal_pos (hmH' v).1 (hmH' v).2)
      (ENNReal.ofReal_toReal (hmH v).2).symm (ENNReal.ofReal_toReal (hmH' v).2).symm
      (cN v).toReal (cN' v).toReal (ENNReal.toReal_pos (hc0 v) (hcT v)) (ENNReal.toReal_pos (hc0' v) (hcT' v)) h hh
    rw [ENNReal.ofReal_toReal (hcT v), ENNReal.ofReal_toReal (hcT' v)] at hP
    exact hP
  · rw [hmuN, pi_smul_factors _ _ hcT, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_prod]
  · rw [hmuN', pi_smul_factors _ _ hcT', Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_prod]

theorem realBracket_of_jac (hJG : JacGauge) (hC : CovolRef) (hA : AprimeInf)
    (hG : ∀ (n : ℕ) (ε : Fin n → Bool), Formalism.MainNotions.S.Gauge.GaugeDens ε) : RealBracket :=
  realBracket_of Formalism.L2.SG.RealObj.InfCut.ProductExactness.ProdExact_holds hA (placeSplit_of hJG hC) hG

end Formalism.L2.SG.Pf.NcReal.JX
end
end
