import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLtAddRootNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLinesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement

section
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.FockSecondSwap

variable {p q r s : ℕ}

def swapLn (p q r s : ℕ) : Ln p q r s ≃ Ln p q s r :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.sumComm _ _)

def lsg (l : Ln p q r s) : ℂ := if linePos l then 1 else -1

def eps : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

def tJ (X : Mat p q) : Mat p q := Matrix.of fun a b => eps a * eps b * X b a

theorem eps_mul_self (a : Ix p q) : eps a * eps a = 1 := by
  rcases a with a | a <;> simp [eps]

theorem linePos_swapLn (l : Ln p q r s) : linePos (swapLn p q r s l) = !linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> rfl

theorem trace_tJ (X : Mat p q) : (tJ X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, tJ, Matrix.of_apply, eps_mul_self, one_mul]

theorem rename_raiB (l : Ln p q r s) (f : Pol p q r s) :
    rename (swapLn p q r s) (raiB l f) = lsg l • lowB (swapLn p q r s l) (rename (swapLn p q r s) f) := by
  have hd := pderiv_rename (R := ℂ) (swapLn p q r s).injective l f
  unfold raiB lowB lsg
  rw [linePos_swapLn]
  cases h : linePos l <;> simp [hd]

theorem rename_lowB (l : Ln p q r s) (f : Pol p q r s) :
    rename (swapLn p q r s) (lowB l f) = -(lsg l) • raiB (swapLn p q r s l) (rename (swapLn p q r s) f) := by
  have hd := pderiv_rename (R := ℂ) (swapLn p q r s).injective l f
  unfold raiB lowB lsg
  rw [linePos_swapLn]
  cases h : linePos l <;> simp [hd]

theorem rename_omE (l l' : Ln p q r s) (f : Pol p q r s) :
    rename (swapLn p q r s) (omE l l' f) =
      -(lsg l * lsg l') • omE (swapLn p q r s l') (swapLn p q r s l) (rename (swapLn p q r s) f) := by
  have hc := congrArg (fun T : Module.End ℂ (Pol p q s r) => T (rename (swapLn p q r s) f))
    (GlobalTheory.FockCasimir.lowB_mul_raiB (swapLn p q r s l) (swapLn p q r s l'))
  simp only [Module.End.mul_apply, LinearMap.add_apply] at hc
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, map_add, rename_raiB, rename_lowB,
    LinearMap.map_smul, hc]
  by_cases h : l = l'
  · subst h
    simp only [if_true, LinearMap.smul_apply, Module.End.one_apply, map_smul]
    have h1 : lsg l = 1 ∨ lsg l = -1 := by unfold lsg; split_ifs <;> simp
    rcases h1 with h1 | h1 <;> rw [h1] <;> module
  · have h' : swapLn p q r s l ≠ swapLn p q r s l' := fun e => h ((swapLn p q r s).injective e)
    simp only [h, h', Ne.symm h', if_false, LinearMap.zero_apply, add_zero, map_zero]
    module

def swapM (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Matrix (Ln p q s r) (Ln p q s r) ℂ :=
  Matrix.of fun m m' => lsg ((swapLn p q r s).symm m') * lsg ((swapLn p q r s).symm m) *
    Z ((swapLn p q r s).symm m') ((swapLn p q r s).symm m)

theorem rename_omAct (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) (f : Pol p q r s) :
    rename (swapLn p q r s) (omAct p q r s Z f) = -(omAct p q s r (swapM Z) (rename (swapLn p q r s) f)) := by
  simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, rename_omE]
  have e : ∀ h : Ln p q s r → Ln p q s r → Pol p q s r,
      ∑ m, ∑ m', h m m' = ∑ l, ∑ l', h (swapLn p q r s l') (swapLn p q r s l) := by
    intro h
    rw [Finset.sum_comm, ← (swapLn p q r s).sum_comp]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← (swapLn p q r s).sum_comp]
  rw [e]
  simp only [swapM, Matrix.of_apply, Equiv.symm_apply_apply, ← Finset.sum_neg_distrib, smul_smul, neg_smul,
    smul_neg, mul_neg]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring_nf

theorem kron_apply (X : Mat p q) (a b : Ix p q) (c d : Ix r s) :
    (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X (a, c) (b, d) = X a b * (1 : Mat r s) c d := by
  simp [Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply]

theorem swapM_kron (X : Mat p q) :
    swapM ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X) =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat s r) (tJ X) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [swapM, Matrix.of_apply, kron_apply, tJ, swapLn, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.refl_apply, Equiv.sumComm_symm, Equiv.sumComm_apply, Prod.map]
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    simp [lsg, linePos, eps, Matrix.one_apply] <;> split_ifs <;> simp_all [eq_comm]

theorem rename_fockAct1 (X : Mat p q) (f : Pol p q r s) :
    rename (swapLn p q r s) (fockAct1 p q r s X f) = -(fockAct1 p q s r (tJ X) (rename (swapLn p q r s) f)) := by
  simp only [fockAct1, LinearMap.comp_apply]
  rw [rename_omAct, swapM_kron]

end GlobalTheory.FockSecondSwap

namespace GlobalTheory.RealLift

open GlobalTheory.FockSecondSwap

theorem hasForm_swap {P Q R S : ℕ} {x : ℚ} (h : HasForm P Q S R x) : HasForm P Q R S (-x) := by
  obtain ⟨l, hl0, hl⟩ := h
  refine ⟨l.comp (rename (swapLn P Q R S)).toLinearMap, fun h0 => hl0 (LinearMap.ext fun f => ?_), fun X f => ?_⟩
  · have := LinearMap.congr_fun h0 (rename (swapLn P Q R S).symm f)
    simpa [rename_rename, Equiv.self_comp_symm, rename_id] using this
  · simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [rename_fockAct1, map_neg, hl, trace_tJ]
    push_cast
    ring

theorem hasForm_neg_of_formEx : FormEx → ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ S → Q ≤ R → 0 < k → 0 < k' →
    x - Formalism.BasicNotions.TH.cPair S R = k → x + Formalism.BasicNotions.TH.cPair S R = k' → HasForm P Q R S (-x) :=
  fun hF P Q R S x k k' h1 h2 h3 h4 h5 h6 => hasForm_swap (hF P Q S R x k k' h1 h2 h3 h4 h5 h6)

end GlobalTheory.RealLift
end
end

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasForm_neg_of_pair_bounds : GlobalTheory.RealLift.FormEx → ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ S → Q ≤ R → 0 < k → 0 < k' → x - Formalism.BasicNotions.TH.cPair S R = k → x + Formalism.BasicNotions.TH.cPair S R = k' → GlobalTheory.RealLift.HasForm P Q R S (-x) := by
  atlas_forward_decl GlobalTheory.RealLift.hasForm_neg_of_formEx
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nontrivial_lift_module : ∀ (P Q R S : ℕ) (x t : ℚ), GlobalTheory.RealLift.HasForm P Q R S x → ∃ (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr ∧ Nontrivial M.V := by
  first | exact @GlobalTheory.FockQuot.exists_lift | exact GlobalTheory.FockQuot.exists_lift | (intros; apply GlobalTheory.FockQuot.exists_lift <;> assumption)
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_joint_shape_generated : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → Nontrivial M.V → ∃ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => x) μ' ∧ GlobalTheory.RealLift.GenBy M (fun c => μ' c + t) := by
  first | exact @GlobalTheory.RealLift.GenLift.genBy_of_isLift | exact GlobalTheory.RealLift.GenLift.genBy_of_isLift | (intros; apply GlobalTheory.RealLift.GenLift.genBy_of_isLift <;> assumption)
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harmonic_highest_weight : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → ∀ (μ : Formalism.BasicNotions.TH.Ix R S → ℚ) (w : M.V), Formalism.BasicNotions.TH.IsHW M.act μ w → ∃ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec x (fun c => μ c - t) f := by
  first | exact @GlobalTheory.HarmLift.harm_lift | exact GlobalTheory.HarmLift.harm_lift | (intros; apply GlobalTheory.HarmLift.harm_lift <;> assumption)
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.RealLift.SteepHarm

theorem eq_zero_of_euler_of_raise {σ : Type} [DecidableEq σ] (n : ℕ) (x : Fin n × Fin n → σ) (y : Fin n → σ) (hx : Function.Injective x)
    (f : MvPolynomial σ ℂ) (hE : ∑ i, X (y i) * pderiv (y i) f = f)
    (hK : ∀ k : Fin n, ∑ i, X (x (i, k)) * pderiv (y i) f = 0) : f = 0 := by
  set M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ) :=
    (rename x : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom.mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) with hM
  have hdet : M.det ≠ 0 := by
    rw [hM, ← RingHom.map_det]
    intro h0
    apply Matrix.det_mvPolynomialX_ne_zero (Fin n) ℂ
    apply rename_injective x hx
    simpa using h0
  have hv : Matrix.vecMul (fun i => pderiv (y i) f) M = 0 := by
    funext k
    rw [Pi.zero_apply, ← hK k]
    simp [Matrix.vecMul, dotProduct, hM, Matrix.mvPolynomialX, mul_comm]
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  rw [← hE]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show pderiv (y i) f = 0 from congrFun h0 i, mul_zero]

theorem fockAct2_Eab_apply {P Q R S : ℕ} (c d : Ix R S) (g : Pol P Q R S) :
    fockAct2 P Q R S (Eab c d) g = ∑ a : Ix P Q, (raiB (a, c) (lowB (a, d) g) +
      if c = d then (1 / 2 : ℂ) • g else 0) := by
  rw [fockAct2_Eab, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [omE, Prod.mk.injEq, true_and]
  split_ifs <;> simp

theorem not_hw_of_wFree (P Q R S : ℕ) (μ : Ix R S → ℚ) (i : Fin R) (f : Pol P Q R S) (hi : P ≤ (i : ℕ))
    (hμ : μ (.inl i) = cPair P Q + 1)
    (hw : ∀ (j' : Fin Q) (k : Fin R), pderiv ((.inr j', .inl k) : Ix P Q × Ix R S) f = 0)
    (hf : IsHW (fockAct2 P Q R S) μ f) : False := by
  have hPR : P ≤ R := hi.trans (Nat.le_of_lt i.2)
  obtain ⟨hne, hmem⟩ := hf
  rw [GlobalTheory.FockAlg.MinFirst.mem_hwSub] at hmem
  obtain ⟨hwt, hpos⟩ := hmem
  apply hne
  refine eq_zero_of_euler_of_raise P (fun p => ((.inl p.1, .inl (Fin.castLE hPR p.2)) : Ix P Q × Ix R S)) (fun i' => (.inl i', .inl i)) ?_ f ?_ ?_
  · intro p p' h
    simp only [Prod.mk.injEq, Sum.inl.injEq] at h
    exact Prod.ext h.1 (Fin.castLE_injective hPR h.2)
  · have h1 := hwt (.inl i)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have e1 : ∀ x : Fin Q, pderiv ((.inr x, .inl i) : Ix P Q × Ix R S) (X (.inr x, .inl i) * f) = f := by
      intro x; rw [Derivation.leibniz, pderiv_X_self, hw, smul_zero, zero_add, smul_eq_mul, mul_one]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, hμ, cPair] at h1
    push_cast at h1
    linear_combination (norm := module) h1
  · intro k
    have h1 := hpos (.inl (Fin.castLE hPR k)) (.inl i) (by
      show Fin.castLE hPR k < i
      rw [Fin.lt_iff_val_lt_val]; simp; omega)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have hne' : (Sum.inl (Fin.castLE hPR k) : Ix R S) ≠ Sum.inl i := by
      intro h; simp only [Sum.inl.injEq, Fin.ext_iff, Fin.coe_castLE] at h; omega
    have e1 : ∀ x : Fin Q, pderiv ((.inr x, .inl (Fin.castLE hPR k)) : Ix P Q × Ix R S) (X (.inr x, .inl i) * f) = 0 := by
      intro x
      rw [Derivation.leibniz, pderiv_X_of_ne (by simp [hne'.symm]), hw, smul_zero, smul_zero, add_zero]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, hne', if_false, add_zero,
      neg_zero, Finset.sum_const_zero] at h1
    exact h1

theorem not_hw_of_uFree (P Q R S : ℕ) (μ : Ix R S → ℚ) (j : Fin S) (f : Pol P Q R S) (hj : Q ≤ (j : ℕ))
    (hμ : μ (.inr j) = 1 - cPair P Q)
    (hu : ∀ (i' : Fin P) (l : Fin S), pderiv ((.inl i', .inr l) : Ix P Q × Ix R S) f = 0)
    (hf : IsHW (fockAct2 P Q R S) μ f) : False := by
  have hQS : Q ≤ S := hj.trans (Nat.le_of_lt j.2)
  obtain ⟨hne, hmem⟩ := hf
  rw [GlobalTheory.FockAlg.MinFirst.mem_hwSub] at hmem
  obtain ⟨hwt, hpos⟩ := hmem
  apply hne
  refine eq_zero_of_euler_of_raise Q (fun p => ((.inr p.1, .inr (Fin.castLE hQS p.2)) : Ix P Q × Ix R S)) (fun j' => (.inr j', .inr j)) ?_ f ?_ ?_
  · intro p p' h
    simp only [Prod.mk.injEq, Sum.inr.injEq] at h
    exact Prod.ext h.1 (Fin.castLE_injective hQS h.2)
  · have h1 := hwt (.inr j)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have e1 : ∀ x : Fin P, pderiv ((.inl x, .inr j) : Ix P Q × Ix R S) (X (.inl x, .inr j) * f) = f := by
      intro x; rw [Derivation.leibniz, pderiv_X_self, hu, smul_zero, zero_add, smul_eq_mul, mul_one]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, hμ, cPair] at h1
    push_cast at h1
    linear_combination (norm := module) h1
  · intro k
    have h1 := hpos (.inr (Fin.castLE hQS k)) (.inr j) (by
      show Fin.castLE hQS k < j
      rw [Fin.lt_iff_val_lt_val]; simp; omega)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have hne' : (Sum.inr (Fin.castLE hQS k) : Ix R S) ≠ Sum.inr j := by
      intro h; simp only [Sum.inr.injEq, Fin.ext_iff, Fin.coe_castLE] at h; omega
    have e1 : ∀ x : Fin P, pderiv ((.inl x, .inr (Fin.castLE hQS k)) : Ix P Q × Ix R S) (X (.inl x, .inr j) * f) = 0 := by
      intro x
      rw [Derivation.leibniz, pderiv_X_of_ne (by simp [hne'.symm]), hu, smul_zero, smul_zero, add_zero]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, hne', if_false, add_zero,
      neg_zero, Finset.sum_const_zero, zero_add] at h1
    exact h1

theorem coeff_diag {σ : Type} (L : Module.End ℂ (MvPolynomial σ ℂ)) (g : (σ →₀ ℕ) → ℂ)
    (hL : ∀ α, L (monomial α 1) = g α • monomial α 1) (f : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    coeff α (L f) = g α * coeff α f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial β c =>
    have : monomial β c = c • (monomial β (1 : ℂ)) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, hL, coeff_smul, coeff_smul, coeff_smul, coeff_monomial]
    by_cases h : β = α
    · subst h; simp; ring
    · simp [h]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem coeff_eig {σ : Type} (L : Module.End ℂ (MvPolynomial σ ℂ)) (g : (σ →₀ ℕ) → ℂ)
    (hL : ∀ α, L (monomial α 1) = g α • monomial α 1) (f : MvPolynomial σ ℂ) (c : ℂ) (hf : L f = c • f)
    (α : σ →₀ ℕ) (hα : coeff α f ≠ 0) : g α = c := by
  have h := coeff_diag L g hL f α
  rw [hf, coeff_smul, smul_eq_mul] at h
  exact (mul_right_cancel₀ hα h).symm

theorem trace_Eab_self {p q : ℕ} (a : Ix p q) : (Eab a a).trace = 1 := by
  simp [Eab, Matrix.trace_single_eq_same]

theorem monomial_facts (P Q R S : ℕ) (x : ℚ) (μ : Ix R S → ℚ) (f : Pol P Q R S)
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) (α : (Ix P Q × Ix R S) →₀ ℕ) (hα : coeff α f ≠ 0) :
    (∀ i' : Fin P, ∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ) = x - cPair R S) ∧
    (∀ j' : Fin Q, ∑ l : Fin S, (α (.inr j', .inr l) : ℚ) - ∑ k : Fin R, (α (.inr j', .inl k) : ℚ) = x + cPair R S) ∧
    (∀ k : Fin R, ∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ) = μ (.inl k) - cPair P Q) ∧
    (∀ l : Fin S, ∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ) - ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ) = μ (.inr l) + cPair P Q) := by
  obtain ⟨_, hK, hne, hmem⟩ := hf
  rw [GlobalTheory.FockAlg.MinFirst.mem_hwSub] at hmem
  have e1 : ∀ a : Ix P Q, (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (x : ℂ) := by
    intro a
    have h := hK (Eab a a) (GlobalTheory.FockAlg.MinFirst.isKC_diag a)
    rw [trace_Eab_self, mul_one] at h
    exact coeff_eig _ _ (fun β => cartan1 a β) f _ h α hα
  have e2 : ∀ c : Ix R S, (∑ a, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (μ c : ℂ) := by
    intro c
    have h := hmem.1 c
    rw [sub_eq_zero] at h
    exact coeff_eig _ _ (fun β => cartan2 c β) f _ h α hα
  refine ⟨fun i' => ?_, fun j' => ?_, fun k => ?_, fun l => ?_⟩
  · have h := e1 (.inl i')
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ) + R / 2 - S / 2 : ℚ) : ℂ) = (x : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith
  · have h := e1 (.inr j')
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ l : Fin S, (α (.inr j', .inr l) : ℚ) - ∑ k : Fin R, (α (.inr j', .inl k) : ℚ) - R / 2 + S / 2 : ℚ) : ℂ) = (x : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith
  · have h := e2 (.inl k)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ) + P / 2 - Q / 2 : ℚ) : ℂ) = (μ (.inl k) : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith
  · have h := e2 (.inr l)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ) - ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ) - P / 2 + Q / 2 : ℚ) : ℂ) = (μ (.inr l) : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith

theorem sum_fin_ite_lt (P R : ℕ) (hPR : P ≤ R) (a b : ℚ) :
    ∑ k : Fin R, (if (k : ℕ) < P then a else b) = P * a + ((R - P : ℕ) : ℚ) * b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < P then a else b) R]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hPR
  rw [Finset.sum_range_add]
  simp [Finset.sum_ite_of_true, Finset.sum_range]

theorem monomial_cols (P Q R S : ℕ) (x : ℚ) (μ : Ix R S → ℚ) (f : Pol P Q R S)
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) (α : (Ix P Q × Ix R S) →₀ ℕ) (hα : coeff α f ≠ 0) :
    ∑ y, (α y : ℚ) = degW (cPair P Q) μ := by
  obtain ⟨hh, _, hne, hmem⟩ := hf
  obtain ⟨W, fW, hP, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  have hOT := ((GlobalTheory.BlockReps.finite_module_structure R S _ (fockAct2 P Q R S) GlobalTheory.FockAlg.MinFirst.kLie2 W fW sW
    fun v _ => GlobalTheory.FockAlg.MinFirst.wts2 v).2.2.2 μ f hP ⟨hne, hmem⟩).2.1
  obtain ⟨d, hd, hhom⟩ := (harmonic_homog_of_type P Q R S).2 μ f hne hOT hh
  rw [mem_homogeneousSubmodule] at hhom
  have h := hhom hα
  rw [← hd, ← h]
  simp [Finsupp.weight_apply, Finsupp.sum_fintype]

theorem alpha_beta_ge_one (P Q P' Q' R S : ℕ) (κ : ℤ) (hN : GlobalTheory.RealLift.Num P Q P' Q' R S κ) :
    1 ≤ (κ : ℚ) / 2 - cPair R S ∧ 1 ≤ (κ : ℚ) / 2 + cPair R S := by
  obtain ⟨_, _, _, _, ⟨n, hn⟩, ⟨m, hm⟩, hκ⟩ := hN
  have hmn : (n : ℤ) + 1 ≤ m := by
    have : ((R + S : ℕ) : ℤ) = n + n := by exact_mod_cast hn
    omega
  have hmn' : (n : ℚ) + 1 ≤ m := by exact_mod_cast hmn
  have hκq : (κ : ℚ) = m + m := by exact_mod_cast hm
  have hnq : (R : ℚ) + S = n + n := by exact_mod_cast hn
  have hR : (0 : ℚ) ≤ R := Nat.cast_nonneg _
  have hS : (0 : ℚ) ≤ S := Nat.cast_nonneg _
  simp only [cPair]
  constructor <;> linarith

theorem col_pure (P Q R S : ℕ) (x : ℚ) (μ : Ix R S → ℚ) (f : Pol P Q R S)
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) (α : (Ix P Q × Ix R S) →₀ ℕ) (hα : coeff α f ≠ 0) :
    (∀ k : Fin R, 0 ≤ μ (.inl k) - cPair P Q → ∀ j' : Fin Q, α (.inr j', .inl k) = 0) ∧
    (∀ l : Fin S, 0 ≤ μ (.inr l) + cPair P Q → ∀ i' : Fin P, α (.inl i', .inr l) = 0) := by
  obtain ⟨_, _, F3, F4⟩ := monomial_facts P Q R S x μ f hf α hα
  have F5 := monomial_cols P Q R S x μ f hf α hα
  let A : Ix R S → ℚ := fun c => match c with
    | .inl k => ∑ i' : Fin P, (α (.inl i', .inl k) : ℚ)
    | .inr l => ∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ)
  let B : Ix R S → ℚ := fun c => match c with
    | .inl k => ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)
    | .inr l => ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ)
  have hA : ∀ c, 0 ≤ A c := by
    rintro (k | l) <;> exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hB : ∀ c, 0 ≤ B c := by
    rintro (k | l) <;> exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hν : ∀ c, A c - B c = shiftNu (cPair P Q) μ c := by
    rintro (k | l)
    · exact F3 k
    · exact F4 l
  have hsum : ∑ c, (A c + B c) = ∑ c, |A c - B c| := by
    simp only [hν]
    rw [show ∑ c, |shiftNu (cPair P Q) μ c| = degW (cPair P Q) μ from rfl, ← F5]
    rw [Fintype.sum_prod_type_right, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [A, B, Fintype.sum_sum_type, Finset.sum_add_distrib]
    ring
  have hle : ∀ c ∈ Finset.univ, |A c - B c| ≤ A c + B c := fun c _ =>
    abs_le.2 ⟨by linarith [hA c, hB c], by linarith [hA c, hB c]⟩
  have hpure := (Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm
  have hB0 : ∀ c, 0 ≤ A c - B c → B c = 0 := by
    intro c hc
    have := hpure c (Finset.mem_univ _)
    rw [abs_of_nonneg hc] at this
    linarith [hB c]
  constructor
  · intro k hk j'
    have h0 : B (.inl k) = 0 := hB0 (.inl k) (by have := hν (.inl k); simp only [shiftNu] at this; linarith)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.cast_nonneg _)).1 h0 j' (Finset.mem_univ _)
    exact_mod_cast this
  · intro l hl i'
    have h0 : B (.inr l) = 0 := hB0 (.inr l) (by have := hν (.inr l); simp only [shiftNu] at this; linarith)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.cast_nonneg _)).1 h0 i' (Finset.mem_univ _)
    exact_mod_cast this

theorem pderiv_eq_zero_of_coeff {σ : Type} [DecidableEq σ] (f : MvPolynomial σ ℂ) (v : σ)
    (h : ∀ α, coeff α f ≠ 0 → α v = 0) : pderiv v f = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  rw [mem_vars] at hv
  obtain ⟨α, hα, hαv⟩ := hv
  exact (Finsupp.mem_support_iff.1 hαv) (h α (mem_support_iff.1 hα))

theorem harm_shape_inl_inr : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S)
    (f : Pol P Q R S), GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j)) f →
    Q ≤ (j : ℕ) ∧ ∀ (j' : Fin Q) (k : Fin R), pderiv ((.inr j', .inl k) : Ix P Q × Ix R S) f = 0 := by
  intro P Q P' Q' R S κ hN i j f hf
  obtain ⟨hα1, hβ1⟩ := alpha_beta_ge_one P Q P' Q' R S κ hN
  have hPR : P ≤ R := by rw [hN.1]; omega
  set μ := GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j) with hμ
  have hμl : ∀ k : Fin R, μ (.inl k) - cPair P Q =
      (if (k : ℕ) < P then (κ : ℚ) / 2 - cPair R S else 0) + (if k = i then 1 else 0) := by
    intro k
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inl.injEq, reduceCtorEq, if_false, sub_zero]
    split_ifs <;> ring
  have hμr : ∀ l : Fin S, μ (.inr l) + cPair P Q =
      (if (l : ℕ) < Q then (κ : ℚ) / 2 + cPair R S else 0) - (if l = j then 1 else 0) := by
    intro l
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inr.injEq, reduceCtorEq, if_false, add_zero]
    split_ifs <;> ring
  have key : ∀ α, coeff α f ≠ 0 → (∀ (j' : Fin Q) (k : Fin R), α (.inr j', .inl k) = 0) ∧ Q ≤ (j : ℕ) := by
    intro α hα0
    obtain ⟨cw, cu⟩ := col_pure P Q R S _ μ f hf α hα0
    have hw : ∀ (k : Fin R) (j' : Fin Q), α (.inr j', .inl k) = 0 := fun k =>
      cw k (by rw [hμl]; split_ifs <;> linarith)
    refine ⟨fun j' k => hw k j', ?_⟩
    by_contra hj
    push_neg at hj
    have hu : ∀ (l : Fin S) (i' : Fin P), α (.inl i', .inr l) = 0 := fun l =>
      cu l (by rw [hμr]; split_ifs <;> first | linarith | (subst_vars; omega))
    obtain ⟨F1, _, F3, _⟩ := monomial_facts P Q R S _ μ f hf α hα0
    have s1 : ∑ i' : Fin P, (∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ)) =
        P * ((κ : ℚ) / 2 - cPair R S) := by
      rw [Finset.sum_congr rfl (fun i' _ => F1 i')]; simp [mul_sub]
    have s3 : ∑ k : Fin R, (∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)) =
        ∑ k : Fin R, (μ (.inl k) - cPair P Q) := Finset.sum_congr rfl fun k _ => F3 k
    simp only [hu, hw, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at s1 s3
    rw [Finset.sum_congr rfl (fun k _ => hμl k), Finset.sum_add_distrib, sum_fin_ite_lt P R hPR] at s3
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero, add_zero] at s3
    rw [Finset.sum_comm] at s3
    linarith
  obtain ⟨α, hα0⟩ := ne_zero_iff.1 hf.2.2.1
  exact ⟨(key α hα0).2, fun j' k => pderiv_eq_zero_of_coeff f _ fun β hβ => (key β hβ).1 j' k⟩

theorem harm_shape_inr_inl : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S)
    (f : Pol P Q R S), GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i)) f →
    P ≤ (i : ℕ) ∧ ∀ (i' : Fin P) (l : Fin S), pderiv ((.inl i', .inr l) : Ix P Q × Ix R S) f = 0 := by
  intro P Q P' Q' R S κ hN i j f hf
  obtain ⟨hα1, hβ1⟩ := alpha_beta_ge_one P Q P' Q' R S κ hN
  have hPR : P ≤ R := by rw [hN.1]; omega
  set μ := GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i) with hμ
  have hμl : ∀ k : Fin R, μ (.inl k) - cPair P Q =
      (if (k : ℕ) < P then (κ : ℚ) / 2 - cPair R S else 0) - (if k = i then 1 else 0) := by
    intro k
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inl.injEq, reduceCtorEq, if_false, add_zero]
    split_ifs <;> ring
  have hμr : ∀ l : Fin S, μ (.inr l) + cPair P Q =
      (if (l : ℕ) < Q then (κ : ℚ) / 2 + cPair R S else 0) + (if l = j then 1 else 0) := by
    intro l
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero]
    split_ifs <;> ring
  have key : ∀ α, coeff α f ≠ 0 → (∀ (i' : Fin P) (l : Fin S), α (.inl i', .inr l) = 0) ∧ P ≤ (i : ℕ) := by
    intro α hα0
    obtain ⟨cw, cu⟩ := col_pure P Q R S _ μ f hf α hα0
    have hu : ∀ (l : Fin S) (i' : Fin P), α (.inl i', .inr l) = 0 := fun l =>
      cu l (by rw [hμr]; split_ifs <;> linarith)
    refine ⟨fun i' l => hu l i', ?_⟩
    by_contra hi
    push_neg at hi
    have hw : ∀ (k : Fin R) (j' : Fin Q), α (.inr j', .inl k) = 0 := fun k =>
      cw k (by rw [hμl]; split_ifs <;> first | linarith | (subst_vars; omega))
    obtain ⟨F1, _, F3, _⟩ := monomial_facts P Q R S _ μ f hf α hα0
    have s1 : ∑ i' : Fin P, (∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ)) =
        P * ((κ : ℚ) / 2 - cPair R S) := by
      rw [Finset.sum_congr rfl (fun i' _ => F1 i')]; simp [mul_sub]
    have s3 : ∑ k : Fin R, (∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)) =
        ∑ k : Fin R, (μ (.inl k) - cPair P Q) := Finset.sum_congr rfl fun k _ => F3 k
    simp only [hu, hw, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at s1 s3
    rw [Finset.sum_congr rfl (fun k _ => hμl k), Finset.sum_sub_distrib, sum_fin_ite_lt P R hPR] at s3
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero, add_zero] at s3
    rw [Finset.sum_comm] at s3
    linarith
  obtain ⟨α, hα0⟩ := ne_zero_iff.1 hf.2.2.1
  exact ⟨(key α hα0).2, fun i' l => pderiv_eq_zero_of_coeff f _ fun β hβ => (key β hβ).1 i' l⟩

open GlobalTheory.RealLift in

theorem casK_addRoot_lr {R S : ℕ} (μ : Ix R S → ℚ) (i : Fin R) (j : Fin S) :
    casK (addRoot μ (.inl i) (.inr j)) = casK μ + 2 * (μ (.inl i) - μ (.inr j)) + 2 +
      ((R : ℚ) - 1 - 2 * (i : ℕ)) - ((S : ℚ) - 1 - 2 * (j : ℕ)) := by
  simp only [casK, addRoot, Fintype.sum_sum_type]
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero, add_zero, zero_sub]
  have h1 : ∀ k : Fin R, (μ (.inl k) + if k = i then 1 else 0) ^ 2 = μ (.inl k) ^ 2 + (if k = i then 2 * μ (.inl i) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  have h2 : ∀ k : Fin S, (μ (.inr k) - if k = j then 1 else 0) ^ 2 = μ (.inr k) ^ 2 + (if k = j then -2 * μ (.inr j) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  simp only [h1, h2, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

open GlobalTheory.RealLift in

theorem casK_addRoot_rl {R S : ℕ} (μ : Ix R S → ℚ) (i : Fin R) (j : Fin S) :
    casK (addRoot μ (.inr j) (.inl i)) = casK μ + 2 * (μ (.inr j) - μ (.inl i)) + 2 +
      ((S : ℚ) - 1 - 2 * (j : ℕ)) - ((R : ℚ) - 1 - 2 * (i : ℕ)) := by
  simp only [casK, addRoot, Fintype.sum_sum_type]
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero, add_zero, zero_sub, zero_add]
  have h1 : ∀ k : Fin R, (μ (.inl k) - if k = i then 1 else 0) ^ 2 = μ (.inl k) ^ 2 + (if k = i then -2 * μ (.inl i) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  have h2 : ∀ k : Fin S, (μ (.inr k) + if k = j then 1 else 0) ^ 2 = μ (.inr k) ^ 2 + (if k = j then 2 * μ (.inr j) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  simp only [h1, h2, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem casK_lt_inl_inr : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S),
    (i : ℕ) < P → Q ≤ (j : ℕ) → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) <
      GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j)) := by
  intro P Q P' Q' R S κ hN i j hi hj
  rw [casK_addRoot_lr]
  have hj' : ¬ (j : ℕ) < Q := not_lt.2 hj
  simp only [GlobalTheory.RealLift.lam, hi, hj', if_true, if_false, cPair]
  have hk : ((R + S : ℕ) : ℤ) < κ := hN.2.2.2.2.2.2
  have hk' : ((R : ℚ) + S) < (κ : ℚ) := by exact_mod_cast hk
  have hi' : ((i : ℕ) : ℚ) + 1 ≤ P := by exact_mod_cast hi
  have hj'' : (Q : ℚ) ≤ ((j : ℕ) : ℚ) := by exact_mod_cast hj
  push_cast
  linarith

theorem casK_lt_inr_inl : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S),
    (j : ℕ) < Q → P ≤ (i : ℕ) → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) <
      GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i)) := by
  intro P Q P' Q' R S κ hN i j hj hi
  rw [casK_addRoot_rl]
  have hi' : ¬ (i : ℕ) < P := not_lt.2 hi
  simp only [GlobalTheory.RealLift.lam, hj, hi', if_true, if_false, cPair]
  have hk : ((R + S : ℕ) : ℤ) < κ := hN.2.2.2.2.2.2
  have hk' : ((R : ℚ) + S) < (κ : ℚ) := by exact_mod_cast hk
  have hj'' : ((j : ℕ) : ℚ) + 1 ≤ Q := by exact_mod_cast hj
  have hi'' : (P : ℚ) ≤ ((i : ℕ) : ℚ) := by exact_mod_cast hi
  push_cast
  linarith

theorem _root_.GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := by
  intro P Q P' Q' R S κ hN a b hab f hf
  rcases a with i | j <;> rcases b with i' | j'
  · exact absurd trivial hab
  · obtain ⟨hj, hw⟩ := harm_shape_inl_inr P Q P' Q' R S κ hN i j' f hf
    have hi : (i : ℕ) < P := by
      by_contra h
      exact not_hw_of_wFree P Q R S _ i f (not_lt.1 h) (by simp [GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, h]) hw hf.2.2
    exact casK_lt_inl_inr P Q P' Q' R S κ hN i j' hi hj
  · obtain ⟨hi, hu⟩ := harm_shape_inr_inl P Q P' Q' R S κ hN i' j f hf
    have hj : (j : ℕ) < Q := by
      by_contra h
      exact not_hw_of_uFree P Q R S _ j f (not_lt.1 h) (by simp [GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, h]; ring) hu hf.2.2
    exact casK_lt_inr_inl P Q P' Q' R S κ hN i' j hj hi
  · exact absurd trivial hab

end GlobalTheory.RealLift.SteepHarm

end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_lt_add_root : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := by
  first | exact @GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot | exact GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot | (intros; apply GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot <;> assumption)
end

section
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ShapeForced
open Formalism.BasicNotions.TH

theorem getD_replicate_append (m k : ℕ) (u w : ℚ) (i : ℕ) :
    (List.replicate m u ++ List.replicate k w).getD i 0 = if i < m then u else if i < m + k then w else 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : i < m
  · rw [List.getElem?_append_left (by simpa using h1)]; simp [h1]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, h1, if_false, List.getElem?_replicate]
    by_cases h2 : i < m + k
    · simp [h2, show i - m < k by omega]
    · simp [h2, show ¬ i - m < k by omega]

theorem all_eq_of_getD {L : List ℚ} {n : ℕ} {v : ℚ} (hn : L.length = n) (h : ∀ i < n, L.getD i 0 = v) :
    ∀ x ∈ L, x = v := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have := h i (hn ▸ hi)
  rwa [List.getD_eq_getElem _ _ hi] at this

theorem pad_length (a b : List ℤ) (k : ℕ) : (pad a k b).length = a.length + k + b.length := by
  simp [pad]; omega

theorem forced (a b : List ℤ) (n : ℕ) (v : ℚ) (hlen : a.length + b.length ≤ n)
    (h : ∀ i < n, (pad a (n - a.length - b.length) b).getD i 0 = v) :
    (∀ x ∈ a, (x : ℚ) = v) ∧ (∀ x ∈ b, (x : ℚ) = v) ∧ (0 < n - a.length - b.length → (0 : ℚ) = v) := by
  have hall := all_eq_of_getD (by rw [pad_length]; omega) h
  refine ⟨fun x hx => hall _ ?_, fun x hx => hall _ ?_, fun hk => hall _ ?_⟩
  · simp only [pad, List.map_append, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
  · simp only [pad, List.map_append, List.mem_append, List.mem_map]; exact Or.inr ⟨x, hx, rfl⟩
  · simp only [pad, List.map_append, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨0, List.mem_replicate.mpr ⟨by omega, rfl⟩, by simp⟩)

theorem cast_pos_of {l : List ℤ} {v : ℚ} (hv : 0 < v) (hl : ∀ x ∈ l, x < 0) (he : ∀ x ∈ l, (x : ℚ) = v) : l = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have h1 := he x hx
  have h2 : (x : ℚ) < 0 := by exact_mod_cast hl x hx
  linarith

theorem cast_neg_of {l : List ℤ} {v : ℚ} (hv : v < 0) (hl : ∀ x ∈ l, 0 < x) (he : ∀ x ∈ l, (x : ℚ) = v) : l = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have h1 := he x hx
  have h2 : (0 : ℚ) < x := by exact_mod_cast hl x hx
  linarith

theorem map_rep {l : List ℤ} {n : ℕ} {v : ℚ} (hn : l.length = n) (he : ∀ x ∈ l, (x : ℚ) = v) :
    l.map (fun x : ℤ => (x : ℚ)) = List.replicate n v := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [hn], ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact he x hx

end GlobalTheory.ShapeForced

open Formalism.BasicNotions.TH GlobalTheory.ShapeForced in
theorem GlobalTheory.RealLift.jointShape_halfKappa : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → (∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => (κ : ℚ) / 2) μ' → μ' = GlobalTheory.RealLift.lam P Q R S κ) ∧ ∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P' Q' R S (fun _ => -((κ : ℚ) / 2)) μ' → (fun c => μ' c + (κ : ℚ) / 2) = GlobalTheory.RealLift.lam P Q R S κ := by
  intro P Q P' Q' R S κ hN
  obtain ⟨hR, hS, hSP, hSQ', -, -, hlt⟩ := hN
  have hltQ : (R : ℚ) + S < κ := by exact_mod_cast hlt
  constructor
  · rintro μ' ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, had, hcb, h1, h2⟩
    have pA : 0 < (κ : ℚ) / 2 - cPair R S := by unfold cPair; linarith
    have pC : 0 < (κ : ℚ) / 2 + cPair R S := by unfold cPair; linarith
    have hA : ∀ i < P, (pad a (P - a.length - b.length) b).getD i 0 = (κ : ℚ) / 2 - cPair R S := by
      intro i hi
      have := congrFun h1 (.inl ⟨i, hi⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    have hC : ∀ j < Q, (pad c (Q - c.length - d.length) d).getD j 0 = (κ : ℚ) / 2 + cPair R S := by
      intro j hj
      have := congrFun h1 (.inr ⟨j, hj⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    obtain ⟨haA, hbA, hkA⟩ := forced a b P _ hab hA
    obtain ⟨hcC, hdC, hkC⟩ := forced c d Q _ hcd hC
    have hb0 := cast_pos_of pA hb hbA
    have hd0 := cast_pos_of pC hd hdC
    subst hb0 hd0
    have hal : a.length = P := by
      by_contra hne
      have := hkA (by simp; omega)
      linarith
    have hcl : c.length = Q := by
      by_contra hne
      have := hkC (by simp; omega)
      linarith
    have hamap := map_rep hal haA
    have hcmap := map_rep hcl hcC
    funext x
    have := congrFun h2 x
    rcases x with ⟨i, hi⟩ | ⟨j, hj⟩
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hamap, List.map_nil, List.append_nil,
        getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      split_ifs at this ⊢ <;> first | linarith | omega
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hcmap, List.map_nil, List.append_nil,
        getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      split_ifs at this ⊢ <;> first | linarith | omega
  · rintro μ' ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, had, hcb, h1, h2⟩
    have pB : -((κ : ℚ) / 2) - cPair R S < 0 := by unfold cPair; linarith
    have pD : -((κ : ℚ) / 2) + cPair R S < 0 := by unfold cPair; linarith
    have hB : ∀ i < P', (pad a (P' - a.length - b.length) b).getD i 0 = -((κ : ℚ) / 2) - cPair R S := by
      intro i hi
      have := congrFun h1 (.inl ⟨i, hi⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    have hD : ∀ j < Q', (pad c (Q' - c.length - d.length) d).getD j 0 = -((κ : ℚ) / 2) + cPair R S := by
      intro j hj
      have := congrFun h1 (.inr ⟨j, hj⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    obtain ⟨haB, hbB, hkB⟩ := forced a b P' _ hab hB
    obtain ⟨hcD, hdD, hkD⟩ := forced c d Q' _ hcd hD
    have ha0 := cast_neg_of pB ha haB
    have hc0 := cast_neg_of pD hc hcD
    subst ha0 hc0
    have hbl : b.length = P' := by
      by_contra hne
      have := hkB (by simp at hab ⊢; omega)
      linarith
    have hdl : d.length = Q' := by
      by_contra hne
      have := hkD (by simp at hcd ⊢; omega)
      linarith
    have hbmap := map_rep hbl hbB
    have hdmap := map_rep hdl hdD
    funext x
    have := congrFun h2 x
    rcases x with ⟨i, hi⟩ | ⟨j, hj⟩
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hdmap, List.map_nil, List.nil_append,
        List.length_nil, getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      subst hR hS
      unfold cPair at this ⊢
      push_cast at this ⊢
      split_ifs at this ⊢ <;> first | linarith | omega
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hbmap, List.map_nil, List.nil_append,
        List.length_nil, getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      subst hR hS
      unfold cPair at this ⊢
      push_cast at this ⊢
      rw [hbl] at this
      by_cases hjQ : j < Q
      · rw [if_pos (by omega)] at this
        rw [if_pos hjQ]
        linarith
      · rw [if_neg (by omega), if_pos (by omega)] at this
        rw [if_neg hjQ]
        linarith
end

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_shape_forced_lambda : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → (∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => (κ : ℚ) / 2) μ' → μ' = GlobalTheory.RealLift.lam P Q R S κ) ∧ ∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P' Q' R S (fun _ => -((κ : ℚ) / 2)) μ' → (fun c => μ' c + (κ : ℚ) / 2) = GlobalTheory.RealLift.lam P Q R S κ := by
  atlas_forward_decl GlobalTheory.RealLift.jointShape_halfKappa
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyFinite_piTensorSumOfFactorOperators : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := by
  first | exact @GlobalTheory.RealLift.locFin_sumPl | exact GlobalTheory.RealLift.locFin_sumPl | (intros; apply GlobalTheory.RealLift.locFin_sumPl <;> assumption)
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := by
  first | exact @GlobalTheory.RealLift.kLine_of_lineEx | exact GlobalTheory.RealLift.kLine_of_lineEx | (intros; apply GlobalTheory.RealLift.kLine_of_lineEx <;> assumption)
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Classical

section SignAdele

variable {F : Type} [Field F] [NumberField F]

def sgnAd (w : InfinitePlace F) : AF F :=
  (((fun v : InfinitePlace F => (if v = w then -1 else 1 : v.Completion)) : Ainf F), (1 : Af F))

theorem sgnAd_mul_self (w : InfinitePlace F) : sgnAd w * sgnAd w = 1 := by
  refine Prod.ext (funext fun v => ?_) (mul_one _)
  show (if v = w then -1 else 1 : v.Completion) * (if v = w then -1 else 1) = 1
  split_ifs <;> simp

theorem evInf_sgnAd (w v : InfinitePlace F) : evInf F v (sgnAd w) = if v = w then -1 else 1 := rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem piInf_algebraMap {v : InfinitePlace F} (τ : EmbOver E v) (y : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) y) = InfinitePlace.Completion.extensionEmbedding v (evInf F v y) := by
  unfold piInf
  rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply]
  simp [compInf]

theorem at_algebraMap_sgnAd_sub_one (w : InfinitePlace F) :
    At (evI F) (algebraMap (AF F) (AE F E) (sgnAd w) - 1) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have h2 : u * (sgnAd w - 1) = 0 := by
    refine Prod.ext ?_ ?_
    · show u.1 * _ = 0
      rw [h1, zero_mul]
    · show u.2 * ((1 : Af F) - 1) = 0
      rw [sub_self, mul_zero]
  rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul, h2, map_zero]

end SignAdele

theorem even_im_hermitian_sub : Parity := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT w
  let u : (AF F)ˣ := ⟨sgnAd w, sgnAd w, sgnAd_mul_self w, sgnAd_mul_self w⟩
  let z : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u
  have hz : At (evI F) ((z : AE F E) - 1) := at_algebraMap_sgnAd_sub_one w
  have hpi : ∀ v, piInf (B.emb v) (z : AE F E) = if v = w then -1 else 1 := by
    intro v
    show piInf (B.emb v) (algebraMap (AF F) (AE F E) (sgnAd w)) = _
    rw [piInf_algebraMap, evInf_sgnAd]
    split_ifs <;> simp
  have hexp : ∀ m : InfinitePlace F → ℤ,
      ∏ v, (piInf (B.emb v) (z : AE F E) / ‖piInf (B.emb v) (z : AE F E)‖) ^ m v = (-1 : ℂ) ^ m w := by
    intro m
    rw [Finset.prod_eq_single w (fun v _ hv => by rw [hpi, if_neg hv]; simp) (fun h => absurd (Finset.mem_univ w) h),
      hpi, if_pos rfl]
    simp
  have eα := hT.chars.expα z hz
  have eβ := hT.chars.expβ z hz
  rw [hexp] at eα eβ
  have rα : (X.α z : ℂ) = _ := hT.chars.resα u
  have rβ : (X.β z : ℂ) = _ := hT.chars.resβ u
  have hpar : ((-1 : ℂ)) ^ a' = (-1) ^ a := by
    have he := hT.geo.even
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, ((Nat.even_add.1 he).1 ha).neg_one_pow]
    · have ha' : Odd a' := Nat.not_even_iff_odd.1 fun h => Nat.not_even_iff_odd.2 ha ((Nat.even_add.1 he).2 h)
      rw [ha.neg_one_pow, ha'.neg_one_pow]
  have hab : (-1 : ℂ) ^ B.mα w = (-1) ^ B.mβ w := by
    rw [← eα, ← eβ, rα, rβ, hpar]
  rcases Int.even_or_odd (B.mα w - B.mβ w) with h | h
  · exact h
  · exfalso
    have h1 := h.neg_one_zpow (α := ℂ)
    rw [zpow_sub₀ (by norm_num), hab, div_self (zpow_ne_zero _ (by norm_num))] at h1
    norm_num at h1
end GlobalTheory.RealLift
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLift_parity : GlobalTheory.RealLift.Parity := by
  first | exact @GlobalTheory.RealLift.even_im_hermitian_sub | exact GlobalTheory.RealLift.even_im_hermitian_sub | (intros; apply GlobalTheory.RealLift.even_im_hermitian_sub <;> assumption)
end

section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : AE F E) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem map_atPl (p : ∀ i, V i →ₗ[ℂ] W i) (w : ι) (L : Module.End ℂ (V w)) (L' : Module.End ℂ (W w))
    (h : p w ∘ₗ L = L' ∘ₗ p w) : PiTensorProduct.map p ∘ₗ atPl w L = atPl w L' ∘ₗ PiTensorProduct.map p := by
  unfold atPl
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp [h]
  · simp [Function.update_of_ne hi]

theorem map_sumPl (p : ∀ i, V i →ₗ[ℂ] W i) (L : ∀ i, Module.End ℂ (V i)) (L' : ∀ i, Module.End ℂ (W i))
    (h : ∀ i, p i ∘ₗ L i = L' i ∘ₗ p i) : PiTensorProduct.map p ∘ₗ sumPl L = sumPl L' ∘ₗ PiTensorProduct.map p := by
  apply LinearMap.ext; intro x
  simp only [sumPl, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (map_atPl p i (L i) (L' i) (h i)) x

end Tensor

theorem i_multone : GlobalTheory.RealLift.MultOne := GlobalTheory.T.multOne'

theorem i_formex : GlobalTheory.RealLift.FormEx := GlobalTheory.T.FormExists

theorem i_formdual : GlobalTheory.RealLift.FormEx → ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ S → Q ≤ R → 0 < k → 0 < k' → x - Formalism.BasicNotions.TH.cPair S R = k → x + Formalism.BasicNotions.TH.cPair S R = k' → GlobalTheory.RealLift.HasForm P Q R S (-x) := GlobalTheory.T.hasForm_neg_of_pair_bounds

theorem i_quot : ∀ (P Q R S : ℕ) (x t : ℚ), GlobalTheory.RealLift.HasForm P Q R S x → ∃ (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr ∧ Nontrivial M.V := GlobalTheory.T.exists_nontrivial_lift_module

theorem i_gen : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → Nontrivial M.V → ∃ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => x) μ' ∧ GlobalTheory.RealLift.GenBy M (fun c => μ' c + t) := GlobalTheory.T.exists_joint_shape_generated

theorem i_harm : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → ∀ (μ : Formalism.BasicNotions.TH.Ix R S → ℚ) (w : M.V), Formalism.BasicNotions.TH.IsHW M.act μ w → ∃ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec x (fun c => μ c - t) f := GlobalTheory.T.exists_harmonic_highest_weight

theorem i_steepv : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := GlobalTheory.T.casimir_lt_add_root

theorem i_steepw : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P' Q' R S, GlobalTheory.RealLift.IsHarmVec (-((κ : ℚ) / 2)) (fun c => GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b c - (κ : ℚ) / 2) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := GlobalTheory.T.casimir_lt_add_root_neg

theorem i_shape : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → (∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => (κ : ℚ) / 2) μ' → μ' = GlobalTheory.RealLift.lam P Q R S κ) ∧ ∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P' Q' R S (fun _ => -((κ : ℚ) / 2)) μ' → (fun c => μ' c + (κ : ℚ) / 2) = GlobalTheory.RealLift.lam P Q R S κ := GlobalTheory.T.joint_shape_forced_lambda

theorem i_cq : GlobalTheory.RealLift.MultOne → ∀ (R S : ℕ) (M M' : Formalism.BasicNotions.TH.GKMod R S) (Λ : Formalism.BasicNotions.TH.Ix R S → ℚ), GlobalTheory.RealLift.GenBy M Λ → GlobalTheory.RealLift.GenBy M' Λ → GlobalTheory.RealLift.Steep M Λ → GlobalTheory.RealLift.Steep M' Λ → ∃ (N : Formalism.BasicNotions.TH.GKMod R S) (π : M.V →ₗ[ℂ] N.V) (π' : M'.V →ₗ[ℂ] N.V), GlobalTheory.RealLift.IsQuot M N π ∧ GlobalTheory.RealLift.IsQuot M' N π' ∧ Formalism.MainNotions.SchurIrreducible.IrrGK N ∧ GlobalTheory.RealLift.ScalarEnd N := GlobalTheory.T.exists_common_irreducible_quotient

theorem i_locfin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := GlobalTheory.T.isLocallyFinite_piTensorSumOfFactorOperators

theorem i_expact : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := GlobalTheory.T.weakExponential_action_on_fockVectors

theorem i_actslaws : GlobalTheory.RealLift.ActsLaws := GlobalTheory.T.archActionReadings_compatible

theorem i_derex : GlobalTheory.RealLift.DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist

theorem i_fockex : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives

theorem i_vacline : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives

theorem i_polrange : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws

theorem i_genex : GlobalTheory.RealLift.GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist

theorem i_lineex : GlobalTheory.RealLift.LineEx := GlobalTheory.T.unitaryLieElements_generate_oneParamLines

theorem i_kline : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines

theorem i_liescalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine

theorem i_liesecond : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar

theorem i_liefirst : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := GlobalTheory.T.lieFirst_of_lieSecond'

theorem i_frameex : GlobalTheory.RealLift.FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists

theorem i_parity : GlobalTheory.RealLift.Parity := GlobalTheory.T.realLift_parity

theorem comp_isLift {P Q R S : ℕ} {x t : ℚ} {M N : GKMod R S} {pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V} {π : M.V →ₗ[ℂ] N.V}
    (h : IsLift x t M pr) (hπ : IsQuot M N π) : IsLift x t N (π ∘ₗ pr) := by
  refine ⟨hπ.1.comp h.1, fun X f => ?_, fun Y f => ?_⟩
  · simp [h.2.1 X f]
  · simp only [LinearMap.comp_apply]
    rw [← hπ.2, h.2.2 Y f, map_add, map_smul]

theorem onePlace (P Q P' Q' R S : ℕ) (κ : ℤ) (h : Num P Q P' Q' R S κ) :
    ∃ (N : GKMod R S) (p : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] N.V) (p' : Formalism.BasicNotions.TH.Pol P' Q' R S →ₗ[ℂ] N.V),
      IsLift ((κ : ℚ) / 2) 0 N p ∧ IsLift (-((κ : ℚ) / 2)) ((κ : ℚ) / 2) N p' ∧ Formalism.MainNotions.SchurIrreducible.IrrGK N ∧ ScalarEnd N := by
  obtain ⟨hR, hS, hSP, hSQ, ⟨m, hm⟩, ⟨k0, hk0⟩, hlt⟩ := h
  have hk : (0 : ℤ) < k0 - m + S := by omega
  have hk' : (0 : ℤ) < k0 + m - S := by omega
  have ec : cPair R S = (m : ℚ) - S := by
    unfold cPair
    have : (R : ℚ) + S = m + m := by exact_mod_cast hm
    linarith
  have ec' : cPair S R = (S : ℚ) - m := by unfold cPair at *; linarith
  have ek : ((κ : ℚ) / 2) = k0 := by rw [hk0]; push_cast; ring
  have hF : HasForm P Q R S ((κ : ℚ) / 2) :=
    i_formex P Q R S _ (k0 - m + S).toNat (k0 + m - S).toNat (by omega) (by omega) (by omega) (by omega)
      (by rw [ec, ek]; rw [show (((k0 - m + S : ℤ).toNat : ℕ) : ℚ) = ((k0 - m + S : ℤ) : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk.le]; push_cast; ring)
      (by rw [ec, ek]; rw [show (((k0 + m - S : ℤ).toNat : ℕ) : ℚ) = ((k0 + m - S : ℤ) : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk'.le]; push_cast; ring)
  have hF' : HasForm P' Q' R S (-((κ : ℚ) / 2)) :=
    i_formdual i_formex P' Q' R S _ (k0 + m - S).toNat (k0 - m + S).toNat (by omega) (by omega) (by omega) (by omega)
      (by rw [ec', ek]; rw [show (((k0 + m - S : ℤ).toNat : ℕ) : ℚ) = ((k0 + m - S : ℤ) : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk'.le]; push_cast; ring)
      (by rw [ec', ek]; rw [show (((k0 - m + S : ℤ).toNat : ℕ) : ℚ) = ((k0 - m + S : ℤ) : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk.le]; push_cast; ring)
  have hN : Num P Q P' Q' R S κ := ⟨hR, hS, hSP, hSQ, ⟨m, hm⟩, ⟨k0, hk0⟩, hlt⟩
  obtain ⟨M, pr, hM, hMn⟩ := i_quot P Q R S _ 0 hF
  obtain ⟨M', pr', hM', hMn'⟩ := i_quot P' Q' R S _ ((κ : ℚ) / 2) hF'
  obtain ⟨μ, hμ, hg⟩ := i_gen _ _ _ _ _ _ M pr hM hMn
  obtain ⟨μ', hμ', hg'⟩ := i_gen _ _ _ _ _ _ M' pr' hM' hMn'
  have e1 : (fun c => μ c + (0 : ℚ)) = lam P Q R S κ := by
    rw [← (i_shape _ _ _ _ _ _ _ hN).1 μ hμ]; funext c; simp
  have e2 := (i_shape _ _ _ _ _ _ _ hN).2 μ' hμ'
  rw [e1] at hg
  rw [e2] at hg'
  have st : Steep M (lam P Q R S κ) := fun a b hab w hw => by
    obtain ⟨f, hf⟩ := i_harm _ _ _ _ _ _ M pr hM _ w hw
    exact i_steepv _ _ _ _ _ _ _ hN a b hab f (by simpa using hf)
  have st' : Steep M' (lam P Q R S κ) := fun a b hab w hw => by
    obtain ⟨f, hf⟩ := i_harm _ _ _ _ _ _ M' pr' hM' _ w hw
    exact i_steepw _ _ _ _ _ _ _ hN a b hab f hf
  obtain ⟨N, π, π', hπ, hπ', hirr, hsc⟩ := i_cq i_multone R S M M' _ hg hg' st st'
  exact ⟨N, π ∘ₗ pr, π' ∘ₗ pr', comp_isLift hM hπ, comp_isLift hM' hπ', hirr, hsc⟩

section Helpers

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem atPl_eq (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq, MultilinearMap.map_update_add]

theorem atPl_smul (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq, MultilinearMap.map_update_smul]

theorem atPl_one (w : ι) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  rw [atPl_eq, show Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id by
    funext i; by_cases h : i = w
    · subst h; simp; rfl
    · simp [Function.update_of_ne h]]
  exact PiTensorProduct.map_id

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq, MultilinearMap.map_update_zero]

end Helpers

section Exp

variable {V V' Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup Z] [Module ℂ Z]

theorem pow_comm {q : V →ₗ[ℂ] Z} {L : Module.End ℂ V} {L0 : Module.End ℂ Z} (h : q ∘ₗ L = L0 ∘ₗ q) (n : ℕ) (v : V) :
    q ((L ^ n) v) = (L0 ^ n) (q v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, ← LinearMap.comp_apply, h,
      LinearMap.comp_apply]

theorem exp_equiv {q : V →ₗ[ℂ] Z} {q' : V' →ₗ[ℂ] Z} {L U : Module.End ℂ V} {L' U' : Module.End ℂ V'} {L0 : Module.End ℂ Z}
    (hU : IsExp L U) (hU' : IsExp L' U') (h : q ∘ₗ L = L0 ∘ₗ q) (h' : q' ∘ₗ L' = L0 ∘ₗ q') {v : V} {v' : V'}
    (e : q v = q' v') : q (U v) = q' (U' v') := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (q (U v) - q' (U' v'))).1 fun l => ?_)
  rw [map_sub, sub_eq_zero]
  have a := hU v (l ∘ₗ q)
  have b := hU' v' (l ∘ₗ q')
  simp only [LinearMap.comp_apply, pow_comm h, pow_comm h', e] at a b
  exact a.unique b

end Exp

theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Side

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

include Φ in
theorem pol_eq (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ T, f = Φ T := by
  rw [← hrange] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨T, rfl⟩

end Side

section SideW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

end SideW

theorem zero_mem_upq (R S : ℕ) : (0 : Mat R S) ∈ upq R S := by simp [upq]

end GlobalTheory.RealLift.Main
end
end
