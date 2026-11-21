import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdProps
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockMulUnipotentDomain

section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem embOn_single_pf (s : Finset (Fin n)) (a b : s) :
    embOn s (Matrix.single a b (1 : ℂ)) = Matrix.single (a : Fin n) (b : Fin n) 1 := by
  ext i j
  by_cases hi : i = (a : Fin n) <;> by_cases hj : j = (b : Fin n)
  · subst hi hj
    simp [embOn, Matrix.single_apply]
  · simp only [embOn, Matrix.single_apply, hj, and_false, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]
  · simp only [embOn, Matrix.single_apply, hi, false_and, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]
  · simp only [embOn, Matrix.single_apply, hi, false_and, if_false]
    split_ifs with h h' <;> simp_all [Subtype.ext_iff]

theorem deriv_prod_range_sub_mul_prod_ne_zero (n m : ℕ) (hmn : m < n) :
    deriv (fun z : ℂ => (∏ i ∈ Finset.range (n - m), ((i : ℂ) - z)) *
      (∏ i ∈ Finset.range (n - (n - m)), ((i : ℂ) - m - z))) 0 ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
  have hm : n - (n - m) = m := by omega
  rw [hm, hk]
  set C : ℂ → ℂ := fun z => ∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℂ) - z) with hCdef
  set B : ℂ → ℂ := fun z => ∏ i ∈ Finset.range m, ((i : ℂ) - m - z) with hBdef
  have hfun : (fun z : ℂ => (∏ i ∈ Finset.range (k + 1), ((i : ℂ) - z)) *
      ∏ i ∈ Finset.range m, ((i : ℂ) - m - z)) = fun z => (C z * (0 - z)) * B z := by
    funext z
    rw [Finset.prod_range_succ']
    simp [C, B]
  have hC : DifferentiableAt ℂ C 0 := DifferentiableAt.fun_finsetProd (fun i _ => by fun_prop)
  have hB : DifferentiableAt ℂ B 0 := DifferentiableAt.fun_finsetProd (fun i _ => by fun_prop)
  have key : HasDerivAt (fun z => (C z * (0 - z)) * B z) ((C 0 * (-1)) * B 0) 0 := by
    have h := (hC.hasDerivAt.mul ((hasDerivAt_id (0 : ℂ)).const_sub 0)).mul hB.hasDerivAt
    convert h using 1 <;> first | rfl | simp
  rw [hfun, key.deriv]
  have hC0 : C 0 ≠ 0 := by
    simp only [C, sub_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.succ_ne_zero i)
  have hB0 : B 0 ≠ 0 := by
    simp only [B, sub_zero]
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hi' : i < m := Finset.mem_range.mp hi
    rw [sub_ne_zero]
    exact_mod_cast hi'.ne
  simp [hC0, hB0]

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.Rg.Sw.HSt

theorem hasDerivAt_det_one_add {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • M).det) M.trace 0 := by
  set p : ℂ[X] := (1 + (X : ℂ[X]) • M.map C).det with hp
  have e : (fun s : ℂ => (1 + s • M).det) = fun s => p.eval s := by
    funext s
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp [mul_comm]
  rw [e]
  have h := p.hasDerivAt 0
  rwa [hp, Matrix.derivative_det_one_add_X_smul] at h

theorem hasDerivAt_det_add {ι : Type} [Fintype ι] [DecidableEq ι] (A X : Matrix ι ι ℂ) (hA : IsUnit A.det) :
    HasDerivAt (fun s : ℂ => (A + s • X).det) (A.det * (A⁻¹ * X).trace) 0 := by
  have e : (fun s : ℂ => (A + s • X).det) = fun s => A.det * (1 + s • (A⁻¹ * X)).det := by
    funext s
    rw [← det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
  rw [e]
  exact (hasDerivAt_det_one_add (A⁻¹ * X)).const_mul _

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_setK {U : Set (M2 n)} (hU : IsOpen U) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg]
    (ι : Kg → M2 n) (hι : Continuous ι) : IsOpen {x : M2 n | ∀ k, ι k * x ∈ U} := by
  have hc : Continuous fun p : Kg × M2 n => ι p.1 * p.2 :=
    (hι.comp continuous_fst).mul continuous_snd
  have hcl : IsClosed {p : Kg × M2 n | ι p.1 * p.2 ∉ U} := (hU.preimage hc).isClosed_compl
  have himg := isClosedMap_snd_of_compactSpace (X := Kg) (Y := M2 n) _ hcl
  have heq : {x : M2 n | ∀ k, ι k * x ∈ U} = (Prod.snd '' {p : Kg × M2 n | ι p.1 * p.2 ∉ U})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Prod.exists, exists_eq_right, not_exists, not_not]
  rw [heq]
  exact himg.isOpen_compl

private theorem u1_eq_toBlocks₂₁_mul_Cm (y : M2 n) : u1 y = toBlocks₂₁ (y * Cm n) := by
  rw [← fromBlocks_toBlocks y]
  ext i j
  simp [Cm, fromBlocks_multiply, u1, toBlocks₂₁, toBlocks₂₂]

private theorem ub1_eq_toBlocks₁₁_fromBlocks_mul_inv (y : M2 n) :
    ub1 y = toBlocks₁₁ (fromBlocks 1 (Complex.I • 1) 0 0 * y⁻¹) := by
  rw [ub1]
  conv_rhs => rw [← fromBlocks_toBlocks y⁻¹]
  simp [fromBlocks_multiply]

private theorem fromBlocks_I_mul_Cm_mul_fromBlocks_diag (A B : Matrix (Fin n) (Fin n) ℂ) :
    fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n * fromBlocks A 0 0 B =
      fromBlocks A 0 0 1 * (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n) := by
  have h : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n =
      fromBlocks ((2 * Complex.I) • 1) 0 0 0 := by
    simp only [Cm, fromBlocks_multiply]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp
  rw [h, fromBlocks_multiply, fromBlocks_multiply]
  simp

private theorem det_one_add_of_support_blkA_blkB (j : ℕ) (P' : Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ a b, P' a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j) : det (1 + P') = 1 := by
  have hd : ∀ a, P' a a = 0 := by
    intro a
    by_contra h
    obtain ⟨h1, h2⟩ := hP a a h
    simp [blkB] at h2
    exact h2 h1
  rw [Matrix.det_of_upperTriangular]
  · simp [hd]
  · intro a b hab
    have hab' : (b : ℕ) < a := hab
    have hne : a ≠ b := fun h => by subst h; omega
    simp only [Matrix.add_apply, Matrix.one_apply, hne, if_false, zero_add]
    by_contra h
    obtain ⟨h1, h2⟩ := hP a b h
    simp [blkA, blkB] at h1 h2
    omega

private theorem det_one_add_of_support_blkB_blkA (j : ℕ) (S' : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ a b, S' a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) : det (1 + S') = 1 := by
  have hd : ∀ a, S' a a = 0 := by
    intro a
    by_contra h
    obtain ⟨h1, h2⟩ := hS a a h
    simp [blkB] at h1
    exact h1 h2
  rw [Matrix.det_of_lowerTriangular]
  · simp [hd]
  · intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hne : a ≠ b := fun h => by subst h; omega
    simp only [Matrix.add_apply, Matrix.one_apply, hne, if_false, zero_add]
    by_contra h
    obtain ⟨h1, h2⟩ := hS a b h
    simp [blkA, blkB] at h1 h2
    omega

theorem Fd_kpart (m j : ℕ) (x : M2 n) (hx : x ∈ Dom n)
    (P' S' : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P' a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S' a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) : Fd m (x * mX (1 + P') 0 0 (1 + S')) = Fd m x := by
  have hPd : det (1 + P') = 1 := det_one_add_of_support_blkA_blkB j P' hP
  have hSd : det (1 + S') = 1 := det_one_add_of_support_blkB_blkA j S' hS
  have hPu : IsUnit (det (1 + P')) := by rw [hPd]; exact isUnit_one
  have hSu : IsUnit (det (1 + S')) := by rw [hSd]; exact isUnit_one
  have hCi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hCii : (Cmi n)⁻¹ = Cm n := Matrix.inv_eq_right_inv cmi_mul_cm
  have hCC : Cm n * Cmi n = 1 := mul_eq_one_comm.mp cmi_mul_cm
  have hg : mX (1 + P') 0 0 (1 + S') = Cm n * fromBlocks (1 + P') 0 0 (1 + S') * Cmi n := by
    rw [mX, hCi]
  have hDinv : (fromBlocks (1 + P') 0 0 (1 + S'))⁻¹ = fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [fromBlocks_multiply]
    simp [Matrix.nonsing_inv_mul _ hPu, Matrix.nonsing_inv_mul _ hSu]
  have hu : u1 (x * mX (1 + P') 0 0 (1 + S')) = u1 x * (1 + P') := by
    rw [u1_eq_toBlocks₂₁_mul_Cm, u1_eq_toBlocks₂₁_mul_Cm x, hg]
    have h : x * (Cm n * fromBlocks (1 + P') 0 0 (1 + S') * Cmi n) * Cm n =
        (x * Cm n) * fromBlocks (1 + P') 0 0 (1 + S') := by
      simp only [Matrix.mul_assoc, cmi_mul_cm, Matrix.mul_one]
    rw [h]
    conv_lhs => rw [← fromBlocks_toBlocks (x * Cm n)]
    rw [fromBlocks_multiply]
    simp
  have hub : ub1 (x * mX (1 + P') 0 0 (1 + S')) = (1 + P')⁻¹ * ub1 x := by
    rw [ub1_eq_toBlocks₁₁_fromBlocks_mul_inv, ub1_eq_toBlocks₁₁_fromBlocks_mul_inv x, hg, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev, hCii, hDinv, hCi]
    have h : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 *
        (Cm n * (fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹ * Cmi n) * x⁻¹) =
        fromBlocks (1 + P')⁻¹ 0 0 1 * (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * x⁻¹) := by
      have h3 := fromBlocks_I_mul_Cm_mul_fromBlocks_diag (n := n) (1 + P')⁻¹ (1 + S')⁻¹
      calc _ = (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * Cm n *
              fromBlocks (1 + P')⁻¹ 0 0 (1 + S')⁻¹) * Cmi n * x⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [h3]
            simp only [Matrix.mul_assoc, hCC, Matrix.one_mul]
    rw [h]
    conv_lhs => rw [← fromBlocks_toBlocks (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 * x⁻¹)]
    rw [fromBlocks_multiply]
    simp
  unfold Fd
  congr 1
  funext z
  simp only [fz]
  rw [hu, hub, det_mul, det_mul, det_mul, hPd, Matrix.det_nonsing_inv, hPd]
  simp

private theorem u2_eq_toBlocks₂₂_mul_Cm (y : M2 n) : u2 y = toBlocks₂₂ (y * Cm n) := by
  rw [← fromBlocks_toBlocks y]
  ext i j
  simp [Cm, fromBlocks_multiply, u2, toBlocks₂₁, toBlocks₂₂]

theorem fderiv_fV_R (m : ℕ) (x : M2 n) (hx : x ∈ Dom n) (a0 b0 : Fin n) :
    fderiv ℂ (fV (n := n) (m : ℤ) 0) x (x * WD 0 (Matrix.single a0 b0 1)) =
      ((m : ℂ) - n) * ((u1 x)⁻¹ * u2 x) b0 a0 * fV (m : ℤ) 0 x := by
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a0 b0 1 with hE
  obtain ⟨hdx, hd1, hd2, hdb⟩ := hx
  have hCi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hCC : Cm n * Cmi n = 1 := mul_eq_one_comm.mp cmi_mul_cm
  have hline : ∀ t : ℂ, x + t • (x * WD 0 E) = x * mX 1 0 (t • E) 1 := by
    intro t
    have h : mX 1 0 (t • E) 1 = 1 + t • WD 0 E := by
      simp only [mX, WD, hCi]
      have h' : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 (t • E) 1 : M2 n) =
          1 + t • (fromBlocks 0 0 E 0 : M2 n) := by
        rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
        simp
      rw [h', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hCC, Matrix.mul_smul, Matrix.smul_mul]
    rw [h, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hu1 : ∀ t : ℂ, u1 (x * mX 1 0 (t • E) 1) = u1 x + t • (u2 x * E) := by
    intro t
    rw [u1_eq_toBlocks₂₁_mul_Cm, u1_eq_toBlocks₂₁_mul_Cm x, u2_eq_toBlocks₂₂_mul_Cm x, mX, hCi]
    have h : x * (Cm n * fromBlocks 1 0 (t • E) 1 * Cmi n) * Cm n =
        (x * Cm n) * fromBlocks 1 0 (t • E) 1 := by
      simp only [Matrix.mul_assoc, cmi_mul_cm, Matrix.mul_one]
    rw [h]
    conv_lhs => rw [← fromBlocks_toBlocks (x * Cm n)]
    rw [fromBlocks_multiply]
    simp [Matrix.mul_smul]
  have hub : ∀ t : ℂ, ub1 (x * mX 1 0 (t • E) 1) = ub1 x := by
    intro t
    rw [inverse_first_block_mul_unipotent_domain x ⟨hdx, hd1, hd2, hdb⟩ 0 (t • E) (by simp) (by simp)]
    simp
  have hg : (fun t : ℂ => fV (n := n) (m : ℤ) 0 (x + t • (x * WD 0 E))) =
      fun t : ℂ => (u1 x + t • (u2 x * E)).det ^ ((m : ℤ) - n) * (ub1 x).det ^ (-(n : ℤ)) := by
    funext t
    rw [hline, fV, hu1, hub]
    simp
  have hdiff : DifferentiableAt ℂ (fV (n := n) (m : ℤ) 0) x :=
    ((contDiffOn_fV (m : ℤ) 0).contDiffAt (isOpen_dom.mem_nhds ⟨hdx, hd1, hd2, hdb⟩)).differentiableAt
      (by simp)
  have hL := ((hasDerivAt_id (0 : ℂ)).smul_const (x * WD 0 E)).const_add x
  simp only [id, one_smul] at hL
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hdet := hasDerivAt_det_add (u1 x) (u2 x * E) (isUnit_iff_ne_zero.mpr hd1)
  have h2 := ((hasDerivAt_zpow ((m : ℤ) - n) ((u1 x + (0 : ℂ) • (u2 x * E)).det)
    (Or.inl (by simpa using hd1))).comp (0 : ℂ) hdet).mul_const ((ub1 x).det ^ (-(n : ℤ)))
  have h1' : HasDerivAt (fun t : ℂ => fV (n := n) (m : ℤ) 0 (x + t • (x * WD 0 E)))
      (fderiv ℂ (fV (n := n) (m : ℤ) 0) x (x * WD 0 E)) 0 := h1
  rw [hg] at h1'
  rw [h1'.unique h2]
  simp only [zero_smul, add_zero]
  rw [← Matrix.mul_assoc, hE, trace_mul_single, fV, zpow_sub_one₀ hd1]
  simp only [zpow_zero, mul_one, MulOpposite.op_one, one_smul, Int.cast_sub, Int.cast_natCast]
  field_simp

end PositivityTheory.Rg.Sw.HSt
end
end
