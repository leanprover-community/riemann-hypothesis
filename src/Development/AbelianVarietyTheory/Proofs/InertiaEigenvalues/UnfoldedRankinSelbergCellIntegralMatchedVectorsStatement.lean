import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuperDiagBlockGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSupSFinGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfNotAntitoneInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProduc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSchurSquareCellProductEqEulerProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergCellIntegralFinitePartNonnegStatement

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.FourierCell

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors SchwartzMap

variable {E : Type} [Field E] [NumberField E]

theorem finId_val (u : (Af E)ˣ) :
    ((finId E u : (Ad E)ˣ) : Ad E) = ((1, (u : Af E)) : InfiniteAdeleRing E × Af E) := by
  change (1 - sFin E 1 + sFin E (u : Af E) : Ad E) = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp
  · change (1 : Af E) - 1 + (u : Af E) = u
    simp

theorem mem_one_iff (x : Af E) :
    x ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 E)⁰ E)ˣ) ↔ ∀ v, Valued.v (pLoc E v x) ≤ 1 := by
  simp only [mem_idealFiniteAdeles, Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  rfl

theorem val_zpow_unif {w : HeightOneSpectrum (𝓞 E)} {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (n : ℤ) :
    Valued.v (ϖ ^ n) = ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, h, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  simp

theorem ofAdd_le_one_iff (n : ℤ) :
    ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 ↔ n ≤ 0 := by
  rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]

theorem exists_fourier_gauss_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (y₀ : Fin (m + 1) → Ad E),
    (∀ w ∉ S, ∀ j, pLoc E w (pFin E (y₀ j)) ∈ w.adicCompletionIntegers E) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
      Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) ∧
      (∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧
        (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0) ∧
      0 < (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y₀).re ∧
      ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
      ∀ a : HeightOneSpectrum (𝓞 E) →₀ ℤ, (∀ v ∈ S, a v = 0) →
      ∀ y : Fin (m + 1) → Ad E,
        (∀ w ∉ S, (∀ j, pLoc E w (pFin E (y j)) ∈ w.adicCompletionIntegers E) ∧
          ∃ j, Valued.v (pLoc E w (pFin E (y j))) = 1) →
        ((∀ w, 0 ≤ a w) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) =
          GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y) ∧
        ((∃ w, a w < 0) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = 0) := by
  intro E _ _ _ m S y₀ hy₀
  classical
  let φ : 𝓢(Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidean (E := Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E))
      (GroundTheory.Global.gaussianSchwartz _)
  have hφ : ∀ x, φ x = ((Real.exp (-Real.pi * ‖toEuclidean x‖ ^ 2) : ℝ) : ℂ) := fun x => by
    simp [φ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  let g : (Fin (m + 1) → Af E) → ℂ := finiteTensor fun j => cosetIndicator 1 (pFin E (y₀ j))
  have hg : g ∈ finiteSchwartzBruhatPi E :=
    finiteTensor_mem fun j => cosetIndicator_mem_finiteSchwartzBruhat _ _
  let G := schwartzBruhatTensorPi φ g
  have hG : G ∈ schwartzBruhatPi E (Fin (m + 1)) := schwartzBruhatTensorPi_mem φ hg
  have hG1 := adelicFourierPi_mem_schwartzBruhatPi hG
  have hG2 := adelicFourierPi_mem_schwartzBruhatPi hG1
  have hG3 := adelicFourierPi_mem_schwartzBruhatPi hG2
  have hFG : adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) = G := by
    rw [adelicFourierPi_adelicFourierPi hG2, adelicFourierPi_adelicFourierPi hG]
    funext x
    simp
  have hGv : ∀ y, G y = φ (infPartPi y) *
      if ∀ j v, Valued.v (pLoc E v (pFin E (y j)) - pLoc E v (pFin E (y₀ j))) ≤ 1 then 1 else 0 := by
    intro y
    simp only [G, g, schwartzBruhatTensorPi, finiteTensor, cosetIndicator_apply, Finset.prod_boole,
      Finset.mem_univ, true_implies, mem_one_iff, map_sub]
    rfl
  refine ⟨adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G)), hG3, ?_, ?_, ?_, ?_⟩
  · rw [hFG]; exact continuous_of_mem_schwartzBruhatPi hG
  · intro y
    rw [hFG, hGv, hφ]
    split_ifs
    · rw [mul_one]
      exact ⟨by rw [Complex.ofReal_re]; exact (Real.exp_pos _).le, Complex.ofReal_im _⟩
    · rw [mul_zero]
      exact ⟨le_refl _, rfl⟩
  · rw [hFG, hGv, hφ, if_pos (fun j v => by simp)]
    rw [mul_one, Complex.ofReal_re]
    exact Real.exp_pos _
  · intro ϖ hϖ a ha y hy
    have hFy : ∀ z, adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) z = G z :=
      fun z => by rw [hFG]
    have hinf : infPartPi (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = infPartPi y := by
      funext j
      simp only [infPartPi, finId_val]
      congr 1
      change (1 : InfiniteAdeleRing E) * (y j).1 = (y j).1
      exact one_mul _
    have hfin : ∀ j v, pLoc E v (pFin E (((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j)) =
        ((ϖ v : v.adicCompletion E) ^ a v) * pLoc E v (pFin E (y j)) := by
      intro j v
      rw [map_mul, map_mul, finId_val]
      change ((ϖ v ^ a v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * _ = _
      rw [Units.val_zpow_eq_zpow_val]
    have hint : ∀ w ∉ S, ∀ j, Valued.v (pLoc E w (pFin E (y₀ j))) ≤ 1 := fun w hw j => by
      simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using hy₀ w hw j
    constructor
    · intro hpos
      rw [hFy, hFy, hGv, hGv, hinf]
      congr 1
      refine if_congr ?_ rfl rfl
      refine forall_congr' fun j => forall_congr' fun v => ?_
      rw [hfin]
      by_cases hv : v ∈ S
      · rw [ha v hv, zpow_zero, one_mul]
      · have h1 := hint v hv j
        have h2 : Valued.v (pLoc E v (pFin E (y j))) ≤ 1 := by
          simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using (hy v hv).1 j
        have h3 : Valued.v ((ϖ v : v.adicCompletion E) ^ a v) ≤ 1 := by
          rw [val_zpow_unif (hϖ v), ofAdd_le_one_iff]
          linarith [hpos v]
        have key : ∀ t, Valued.v t ≤ 1 → Valued.v (t - pLoc E v (pFin E (y₀ j))) ≤ 1 :=
          fun t ht => (Valuation.map_sub _ _ _).trans (max_le ht h1)
        exact iff_of_true (key _ (by rw [map_mul]; exact mul_le_one' h3 h2)) (key _ h2)
    · rintro ⟨w, hw⟩
      rw [hFy, hGv, if_neg, mul_zero]
      intro hP
      have hwS : w ∉ S := fun h => by rw [ha w h] at hw; exact lt_irrefl _ hw
      obtain ⟨j, hj⟩ := (hy w hwS).2
      have h1 := hint w hwS j
      have h := hP j w
      rw [hfin] at h
      have ht : Valued.v ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j))) ≤ 1 := by
        have h4 := Valuation.map_add Valued.v
          ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j)) - pLoc E w (pFin E (y₀ j)))
          (pLoc E w (pFin E (y₀ j)))
        rw [sub_add_cancel] at h4
        exact h4.trans (max_le h h1)
      rw [map_mul, hj, mul_one, val_zpow_unif (hϖ w), ofAdd_le_one_iff] at ht
      omega

end GlobalTheory.FourierCell
end
end

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.CellEvalNM

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

variable {E : Type} [Field E] [NumberField E]

theorem map_blockGL' {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {j n : ℕ} (hj : j ≤ n)
    (g : GL (Fin j) R) :
    Matrix.GeneralLinearGroup.map p (blockGL hj g) = blockGL hj (Matrix.GeneralLinearGroup.map p g) := by
  ext a b
  simp [blockMat_apply]
  split_ifs <;> simp

theorem blockGL_finGL {j n : ℕ} (hj : j ≤ n) (k : GL (Fin j) (Af E)) :
    blockGL hj (finGL E j k) = finGL E n (blockGL hj k) := by
  have hf : ∀ (N : ℕ) (k : GL (Fin N) (Af E)) (a b : Fin N), ((finGL E N k : GA E N) : Matrix (Fin N) (Fin N) (Ad E)) a b =
      (1 : Matrix (Fin N) (Fin N) (Ad E)) a b - sFin E ((1 : Matrix (Fin N) (Fin N) (Af E)) a b) +
        sFin E ((k : Matrix (Fin N) (Fin N) (Af E)) a b) := fun N k a b => rfl
  apply Units.ext
  ext a b
  rw [coe_blockGL, blockMat_apply, hf, coe_blockGL, blockMat_apply]
  split_ifs with h1 h2 h3 <;> simp only [hf, Matrix.one_apply, Fin.ext_iff] <;> split_ifs <;> first | (simp; done) | (exfalso; omega) | (exfalso; simp_all; done) | (simp only [map_zero]; abel)

theorem blockGL_mem_KGL (w : HeightOneSpectrum (𝓞 E)) {j n : ℕ} (hj : j ≤ n) {y : GL (Fin j) (w.adicCompletion E)}
    (hy : y ∈ KGL w j) : blockGL hj y ∈ KGL w n := by
  rw [GlobalTheory.HenQ.Basic.mem_KGL_iff] at hy ⊢
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [coe_blockGL, blockMat_apply]
    split_ifs
    · exact hy.1 _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _
  · rw [← map_inv, coe_blockGL, blockMat_apply]
    split_ifs
    · exact hy.2 _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _

end GlobalTheory.CellEvalNM

namespace GlobalTheory.CellEvalNM

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

theorem eq_zero_of_comp_diag (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)
    (w : HeightOneSpectrum (𝓞 E))
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w)
    (ϖw : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖw : w.adicCompletion E)) (W : GA E N → ℂ)
    (hWN : ∀ u ∈ GlobalTheory.JSW.NA E N, ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g)
    (hWK : ∀ k ∈ KGL w N, ∀ g, W (g * finGL E N (locGL E N w k)) = W g)
    (e : Fin N → ℤ) (he : ¬ Antitone e) (P : GA E N)
    (hP : ((GlobalTheory.CellDec.compV E N w P : GL (Fin N) (w.adicCompletion E)) : Matrix (Fin N) (Fin N) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖw ^ e a : (w.adicCompletion E)ˣ) : w.adicCompletion E)) :
    W P = 0 := by
  set D := GlobalTheory.CellDec.compV E N w P with hD
  set P' := P * (finGL E N (locGL E N w D))⁻¹ with hP'
  have hP'w : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) P' = 1 := by
    change GlobalTheory.CellDec.compV E N w P' = 1
    rw [hP', map_mul, map_inv, GlobalTheory.CellDec.compV_finGL_locGL_same, ← hD, mul_inv_cancel]
  have htt : P' * finGL E N (locGL E N w D) = P := by rw [hP', inv_mul_cancel_right]
  let f : GL (Fin N) (w.adicCompletion E) → ℂ := fun g => W (P' * finGL E N (locGL E N w g))
  have hfD : f D = W P := by simp only [f]; rw [htt]
  have hfN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin N), ∀ g,
      f (u * g) = GlobalTheory.JSW.psiLocChar w (GlobalTheory.Whittaker.superDiag u) * f g := by
    intro u hu g
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc P', GlobalTheory.JSW.commute_finGL_locGL w hP'w, mul_assoc,
      hWN _ (GlobalTheory.JSW.CutTransfer.finGL_locGL_mem_NA' w hu), GlobalTheory.JSW.CutTransfer.psiN_finGL_locGL]
    rfl
  have hfK : ∀ g, ∀ k ∈ KGL w N, f (g * k) = f g := by
    intro g k hk
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc]
    exact hWK k hk _
  have h := GlobalTheory.WhitTorus.eq_zero_of_not_antitone_int E w N (GlobalTheory.JSW.psiLocChar w) hψ f hfN hfK ϖw hϖ e he D hP
  rwa [hfD] at h

variable {E : Type} [Field E] [NumberField E]

theorem lastRow_diag_mul {m : ℕ} (d : Fin (m + 1) → (Ad E)ˣ) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (GlobalTheory.SmGL.diagT (Ad E) (Fin (m + 1)) d * g) =
      fun j => ((d (Fin.last m) : Ad E)) * GlobalTheory.ZEul.lastRow g j := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul]

theorem exists_val_lastRow_eq_one (w : HeightOneSpectrum (𝓞 E)) {m : ℕ} {k : GL (Fin (m + 1)) (w.adicCompletion E)}
    (hk : k ∈ KGL w (m + 1)) : ∃ j, Valued.v ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) = 1 := by
  rw [GlobalTheory.HenQ.Basic.mem_KGL_iff] at hk
  by_contra hne
  push_neg at hne
  have hlt : ∀ j, Valued.v ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) < 1 :=
    fun j => lt_of_le_of_ne (hk.1 _ _) (hne j)
  have h1 : ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) * ((k⁻¹ : GL (Fin (m + 1)) (w.adicCompletion E)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E))) (Fin.last m) (Fin.last m) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  have h2 : Valued.v (∑ j, (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j *
      ((k⁻¹ : GL (Fin (m + 1)) (w.adicCompletion E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) j (Fin.last m)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    calc _ ≤ Valued.v ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) * 1 :=
          by gcongr; exact hk.2 _ _
      _ < 1 := by rw [mul_one]; exact hlt j
  rw [h1, map_one] at h2
  exact lt_irrefl _ h2

end GlobalTheory.CellEvalNM

namespace GlobalTheory.CellEvalNM

open GlobalTheory.RSnmUnf

theorem padNat_self {j : ℕ} (l : Fin j → ℕ) : padNat (n := j) l = l := by
  funext i; simp [padNat]

theorem sphW_pad (q : ℕ) (hq : 0 < q) {j n : ℕ} (hj : j ≤ n) (α : Fin n → ℂ) (v : Fin j → ℤ) (h0 : ∀ i, 0 ≤ v i)
    (hv : Antitone v) :
    sphW q α (padNat fun i => (v i).toNat) =
      (((q : ℝ) ^ (-((GlobalTheory.CellDec.wtS j v : ℝ) + ((n : ℝ) - j) * ∑ i, (v i : ℝ)) / 2) : ℝ) : ℂ) *
        schurAt (padNat fun i => (v i).toNat) α := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : Antitone (padNat (n := n) fun i => (v i).toNat) := by
    intro a b hab
    have hab' : (a : ℕ) ≤ b := hab
    simp only [padNat]
    split_ifs with h1 h2 h2
    · exact Int.toNat_le_toNat (hv (show (⟨a, h2⟩ : Fin j) ≤ ⟨b, h1⟩ from hab'))
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have hcast : ∀ i, (((v i).toNat : ℕ) : ℂ) = ((v i : ℤ) : ℂ) := by
    intro i
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (h0 i)]
  have hc : (∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * ((padNat (n := n) (fun i => (v i).toNat) i : ℕ) : ℂ))) =
      ∑ i : Fin j, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (v i : ℂ)) := by
    symm
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro i hi
      have hij : ¬ (i : ℕ) < j := fun h => hi ⟨⟨i, h⟩, rfl⟩
      simp [padNat, hij]
    · intro i
      simp [padNat, hcast]
  rw [sphW, if_pos hl, hc, Complex.ofReal_cpow hqR.le, GlobalTheory.ZEulLocal.wtS_eq_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem localTerm_mixed (q : ℕ) (hq : 0 < q) {j n : ℕ} (hj : j ≤ n) (α : Fin n → ℂ) (β : Fin j → ℂ) (x y : ℝ)
    (hy : y = x - ((n : ℝ) - j) / 2) (v : Fin j → ℤ) (h0 : ∀ i, 0 ≤ v i) (hv : Antitone v) :
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS j v : ℝ) : ℂ) *
      (sphW q α (padNat fun i => (v i).toNat) * conj (sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-y * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = rsTermNM q α β x v := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hβ := sphW_pad q hq le_rfl β v h0 hv
  rw [padNat_self] at hβ
  have key2 : (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat) := by
    have e : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hqR.le]
      push_cast
      rfl
    rw [e, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    congr 3
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i)).symm
  rw [sphW_pad q hq hj α v h0 hv, hβ, rsTermNM, if_pos ⟨h0, hv⟩, ← key2, map_mul, Complex.conj_ofReal]
  set s : ℝ := ∑ i, (v i : ℝ)
  set A : ℝ := (q : ℝ) ^ (-((GlobalTheory.CellDec.wtS j v : ℝ) + ((n : ℝ) - j) * s) / 2) with hA
  set A' : ℝ := (q : ℝ) ^ (-((GlobalTheory.CellDec.wtS j v : ℝ) + ((j : ℝ) - j) * s) / 2) with hA'
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS j v * (A * A') * (q : ℝ) ^ (-y * s) = (q : ℝ) ^ (-x * s) := by
    rw [hA, hA', ← Real.rpow_intCast, ← Real.rpow_add hqR, ← Real.rpow_add hqR, ← Real.rpow_add hqR, hy]
    congr 1
    ring
  rw [← key]
  push_cast
  ring

theorem localTerm_diag (q : ℕ) (hq : 0 < q) {j n : ℕ} (hj : j ≤ n) (α : Fin n → ℂ) (x y : ℝ)
    (hy : y = x - ((n : ℝ) - j)) (v : Fin j → ℤ) (h0 : ∀ i, 0 ≤ v i) (hv : Antitone v) :
    (q : ℝ) ^ GlobalTheory.CellDec.wtS j v * ‖sphW q α (padNat fun i => (v i).toNat)‖ ^ 2 * (q : ℝ) ^ (-y * ∑ i, (v i : ℝ)) =
      ‖schurAt (padNat (n := n) fun i => (v i).toNat) α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : ((∑ i, (v i).toNat : ℕ) : ℝ) = ∑ i, (v i : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i))
  rw [sphW_pad q hq hj α v h0 hv, hs, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hqR.le _)]
  set s : ℝ := ∑ i, (v i : ℝ)
  set A : ℝ := (q : ℝ) ^ (-((GlobalTheory.CellDec.wtS j v : ℝ) + ((n : ℝ) - j) * s) / 2) with hA
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS j v * (A * A) * (q : ℝ) ^ (-y * s) = (q : ℝ) ^ (-(s * x)) := by
    rw [hA, ← Real.rpow_intCast, ← Real.rpow_add hqR, ← Real.rpow_add hqR, ← Real.rpow_add hqR, hy]
    congr 1
    ring
  rw [← key]
  ring

theorem ennreal_collect {ι : Type} (s : Finset ι) (a e t : ι → ℝ) (p : ι → ℂ) (ha : ∀ w, 0 ≤ a w) (he : ∀ w, 0 ≤ e w)
    (ht : ∀ w ∈ s, a w * ‖p w‖ ^ 2 * e w = t w) (c W : ℂ) (hc : ‖c‖ = 1) (Z : ℝ≥0∞) (D : ℝ) :
    ENNReal.ofReal (∏ w ∈ s, a w) * (‖c * (∏ w ∈ s, p w) * W‖ₑ ^ 2 * Z * ENNReal.ofReal ((∏ w ∈ s, e w) * D)) =
      (∏ w ∈ s, ENNReal.ofReal (t w)) * (‖W‖ₑ ^ 2 * Z * ENNReal.ofReal D) := by
  have h1 : (∏ w ∈ s, ENNReal.ofReal (t w)) =
      ENNReal.ofReal (∏ w ∈ s, a w) * ‖∏ w ∈ s, p w‖ₑ ^ 2 * ENNReal.ofReal (∏ w ∈ s, e w) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun w hw => by rw [← ht w hw]; have := ha w; have := he w; positivity),
      ← Finset.prod_congr rfl ht, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, ← norm_prod,
      ENNReal.ofReal_mul (mul_nonneg (Finset.prod_nonneg fun w _ => ha w) (by positivity)),
      ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => ha w), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have h2 : ‖c‖ₑ = 1 := by rw [← ofReal_norm_eq_enorm, hc, ENNReal.ofReal_one]
  rw [h1, enorm_mul, enorm_mul, h2, ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => he w)]
  ring

end GlobalTheory.CellEvalNM

namespace GlobalTheory.CellEvalNM

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

theorem compV_tl {E : Type} [Field E] [NumberField E] (N : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin N → ℤ)) (w : HeightOneSpectrum (𝓞 E)) :
    ((GlobalTheory.CellDec.compV E N w (GlobalTheory.CellDec.tl N ϖ l) : GL (Fin N) (w.adicCompletion E)) :
      Matrix (Fin N) (Fin N) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ w ^ l w a : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  rw [GlobalTheory.CellDec.tl, GlobalTheory.CellDec.compV_finGL]
  refine Matrix.ext fun i j => ?_
  change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin N) _ : GL (Fin N) (Af E)) : Matrix (Fin N) (Fin N) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin N → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
    simp
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem cell_values (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hψ : ∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hϖ : ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E))
    (g : GA E N) (hg : g ∈ GlobalTheory.CellDec.C0 E N S) (l : GlobalTheory.CellDec.abelian₂ E N S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ V : GA E N → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E N, ∀ g, V (u * g) = GlobalTheory.JSW.psiN u * V g) →
      (∀ k : GL (Fin N) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v N) →
        (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, V (g * finGL E N k) = V g) →
      ((∃ w, ¬ Antitone (l.1 w)) → V (GlobalTheory.CellDec.tl N ϖ l.1 * g) = 0) ∧
      ∀ p : HeightOneSpectrum (𝓞 E) → (Fin N → ℕ) → ℂ,
        (∀ l' : HeightOneSpectrum (𝓞 E) →₀ (Fin N → ℕ), (∀ w ∈ l'.support, w ∉ S) → ∀ h ∈ GlobalTheory.JSW.supS E N S,
          V (h * GlobalTheory.JSW.tl ϖ l') = (∏ w ∈ l'.support, p w (l' w)) * V h) →
        (∀ w i, 0 ≤ l.1 w i) →
        V (GlobalTheory.CellDec.tl N ϖ l.1 * g) = c * (∏ w ∈ l.1.support, p w (fun i => (l.1 w i).toNat)) * V g := by
  obtain ⟨u, hu, h, hh, k, hk, hkS, rfl⟩ := GlobalTheory.CellDec.exists_mul_supS_finGL E N S g hg
  set t := GlobalTheory.CellDec.tl N ϖ l.1 with ht
  have hcomm : h * t = t * h := GlobalTheory.CellDec.TlComm.tl_commute_of_one_off E N S ϖ l h hh
  have hu0 : u ∈ GlobalTheory.JSW.NA E N := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  have hu' : t * u * t⁻¹ ∈ GlobalTheory.JSW.NA E N := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 (GlobalTheory.CellDec.tl_conj_mem ϖ l.1 hu)
  have hσ : t * (u * h * finGL E N k) = (t * u * t⁻¹) * (h * t) * finGL E N k := by
    rw [hcomm]; group
  have hne : GlobalTheory.JSW.psiN u ≠ 0 := norm_ne_zero_iff.1 (by rw [GlobalTheory.RSnmUnfProps.norm_psiN]; exact one_ne_zero)
  refine ⟨GlobalTheory.JSW.psiN (t * u * t⁻¹) * (GlobalTheory.JSW.psiN u)⁻¹, ?_, fun V hN hK => ⟨?_, fun p hp hnn => ?_⟩⟩
  · rw [norm_mul, norm_inv, GlobalTheory.RSnmUnfProps.norm_psiN, GlobalTheory.RSnmUnfProps.norm_psiN, inv_one, mul_one]
  · rintro ⟨w, hw⟩
    have hw0 : l.1 w ≠ 0 := by rintro h0; rw [h0] at hw; exact hw antitone_const
    have hwS : w ∉ S := fun h => hw0 (l.2 w h)
    rw [hσ, hK k hk hkS, hN _ hu', eq_zero_of_comp_diag E N w (hψ w hwS) (ϖ w) (hϖ w) V hN ?_ (l.1 w) hw (h * t) ?_,
      mul_zero]
    · intro k' hk'
      refine hK _ (fun v => ?_) fun v hv => pLoc_locGL_of_ne (fun e : v = w => hwS (e ▸ hv)) k'
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hk'
      · rw [pLoc_locGL_of_ne hvw]; exact one_mem _
    · have h1 : GlobalTheory.CellDec.compV E N w h = 1 := hh w hwS
      rw [map_mul, h1, one_mul]
      exact compV_tl N ϖ l.1 w
  · obtain ⟨l', hl'app⟩ : ∃ l' : HeightOneSpectrum (𝓞 E) →₀ (Fin N → ℕ), ∀ w, l' w = fun i => (l.1 w i).toNat :=
      ⟨Finsupp.mapRange (fun v i => (v i).toNat) (funext fun _ => rfl) l.1, fun w => Finsupp.mapRange_apply⟩
    have hl' : ∀ w i, ((l' w i : ℕ) : ℤ) = l.1 w i := fun w i => by
      rw [hl'app]; exact Int.toNat_of_nonneg (hnn w i)
    have hsupp : l'.support = l.1.support := by
      ext w
      simp only [Finsupp.mem_support_iff, ne_eq]
      constructor
      · intro h h0; apply h; rw [hl'app, h0]; rfl
      · intro h h0; apply h; funext i; have := hl' w i; rw [h0] at this; simpa using this.symm
    have htl : t = GlobalTheory.JSW.tl ϖ l' := GlobalTheory.CellDecNat.tl_eq_jsw_tl E N ϖ l.1 l' hl'
    have hsS : ∀ w ∈ l'.support, w ∉ S := fun w hw hS' => by
      rw [hsupp, Finsupp.mem_support_iff] at hw; exact hw (l.2 w hS')
    have e1 : V (h * t) = (∏ w ∈ l.1.support, p w (fun i => (l.1 w i).toNat)) * V h := by
      rw [htl, hp l' hsS h hh, hsupp]
      simp only [hl'app]
    rw [hσ, hK k hk hkS, hN _ hu', e1, hK k hk hkS, hN _ hu0]
    field_simp

theorem lastRow_prim (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (g : GA E (m + 1)) (hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∉ S) :
    (∀ j, pLoc E w (pFin E (GlobalTheory.ZEul.lastRow g j)) ∈ w.adicCompletionIntegers E) ∧
      ∃ j, Valued.v (pLoc E w (pFin E (GlobalTheory.ZEul.lastRow g j))) = 1 := by
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  rw [GlobalTheory.ZEulProps.lastRow_unip hu]
  have hkw : GlobalTheory.CellDec.compV E (m + 1) w k ∈ KGL w (m + 1) := by
    simp only [GlobalTheory.CellDec.US, Subgroup.mem_iInf, Subgroup.mem_comap] at hk
    exact hk w hw
  have he : ∀ j, pLoc E w (pFin E (GlobalTheory.ZEul.lastRow k j)) = ((GlobalTheory.CellDec.compV E (m + 1) w k : GL (Fin (m + 1)) (w.adicCompletion E)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j := fun j => by
    rw [GlobalTheory.CellDec.compV, Matrix.GeneralLinearGroup.map_apply]; rfl
  obtain ⟨j, hj⟩ := exists_val_lastRow_eq_one w hkw
  refine ⟨fun j => ?_, j, ?_⟩
  · rw [he]; exact ((GlobalTheory.HenQ.Basic.mem_KGL_iff w _).1 hkw).1 (Fin.last m) j
  · rw [he]; exact hj

end GlobalTheory.CellEvalNM

open GroundTheory.Automorphic.FourierWhittaker (blockGL) in
open GlobalTheory.CellEvalNM in

theorem GlobalTheory.CellEvalNM.uIntNM_cell_eval : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (F : (Fin (m + 1) → Ad E) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ k : GL (Fin (m + r + 1 + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + r + 1 + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + r + 1 + 1) k) = GlobalTheory.JSW.whit φ g) →
    (∀ k : GL (Fin (m + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) k) = GlobalTheory.JSW.whit φ' g) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
      ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
        GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
          (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
      ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
        GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
          (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
            GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
    (∀ a : HeightOneSpectrum (𝓞 E) →₀ ℤ, (∀ v ∈ S, a v = 0) →
      ∀ y : Fin (m + 1) → Ad E,
        (∀ w ∉ S, (∀ j, pLoc E w (pFin E (y j)) ∈ w.adicCompletionIntegers E) ∧
          ∃ j, Valued.v (pLoc E w (pFin E (y j))) = 1) →
        ((∀ w, 0 ≤ a w) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y) ∧
        ((∃ w, a w < 0) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = 0)) →
    ∀ (x : ℝ), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
      (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
        (l.1.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (β w i : ℂ)) x v) *
          GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' 0 g * ((GlobalTheory.RSnm.detAbs g ^ x : ℝ) : ℂ) ∧
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g))‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ^ (x - ((r : ℝ) + 1)))) = (l.1.prod fun w v => if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := (m + r + 1 + 1)) fun i => (v i).toNat) (fun i => (α w i : ℂ))‖ ^ 2 *
            (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) * (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (g))‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ (x - ((r : ℝ) + 1)))) ∧
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * (‖GlobalTheory.JSW.whit φ' (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ^ x)) = (l.1.prod fun w v => if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := (m + 1)) fun i => (v i).toNat) (fun i => (β w i : ℂ))‖ ^ 2 *
            (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) * (‖GlobalTheory.JSW.whit φ' (g)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ x)) := by
  intro E _ _ _ m r S hψ ϖ hϖ α β φ φ' F hN hN' hK hK' hS' hS hF x g hg l
  have hmn : m + 1 ≤ m + r + 1 + 1 := by omega
  obtain ⟨c, hc, hV⟩ := cell_values E (m + 1) S hψ ϖ hϖ g hg l
  obtain ⟨hz1, hv1⟩ := hV (fun g => GlobalTheory.JSW.whit φ (blockGL hmn g))
    (fun u hu g => by
      rw [map_mul, hN _ (GlobalTheory.RSnmUnfProps.blockGL_mem_NA hmn hu), GlobalTheory.RSnmUnfProps.psiN_blockGL])
    (fun k hk hkS g => by
      rw [map_mul, blockGL_finGL]
      refine hK _ (fun v => ?_) (fun v hv => ?_) _
      · rw [map_blockGL']; exact blockGL_mem_KGL v hmn (hk v)
      · rw [map_blockGL', hkS v hv, map_one])
  obtain ⟨hz2, hv2⟩ := hV (GlobalTheory.JSW.whit φ') hN' hK'
  have hrow : GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) = fun j =>
      ((finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1)) : (Ad E)ˣ) : Ad E) *
        GlobalTheory.ZEul.lastRow g j := by
    rw [GlobalTheory.CellDec.tl_eq_diagT, lastRow_diag_mul]
  obtain ⟨hF1, hF2⟩ := hF (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1)
    (fun v hv => by rw [Finsupp.mapRange_apply, l.2 v hv]; rfl) (GlobalTheory.ZEul.lastRow g) (lastRow_prim E m S g hg)
  rw [← hrow] at hF1 hF2
  simp only [Finsupp.mapRange_apply] at hF1 hF2
  by_cases hgood : ∀ w, (∀ i, 0 ≤ l.1 w i) ∧ Antitone (l.1 w)
  swap
  · obtain ⟨w, hw⟩ := not_forall.1 hgood
    have hws : w ∈ l.1.support := by
      rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at hw; exact hw ⟨fun _ => le_rfl, antitone_const⟩
    rw [Finsupp.prod, Finsupp.prod, Finsupp.prod, Finset.prod_eq_zero hws (by rw [GlobalTheory.RSnmUnf.rsTermNM, if_neg hw]),
      Finset.prod_eq_zero hws (if_neg hw), Finset.prod_eq_zero hws (if_neg hw), GlobalTheory.RSnmUnf.uIntNM]
    by_cases ha : ∀ w, Antitone (l.1 w)
    · have h0 := hF2 ⟨w, not_le.1 fun h => hw ⟨fun i => le_trans h (ha w (Fin.le_last i)), ha w⟩⟩
      simp [h0]
    · have h1 := hz1 (not_forall.1 ha)
      have h2 := hz2 (not_forall.1 ha)
      rw [h1, h2]
      simp
  have hnn : ∀ w i, 0 ≤ l.1 w i := fun w => (hgood w).1
  have e1 := hv1 (fun w v => GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat v)) hS hnn
  have e2 := hv2 (fun w v => GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) v) hS' hnn
  have e3 := hF1 fun w => hnn w _
  have hq : ∀ w, 0 < qV E w := fun w => Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdet : ∀ y : ℝ, GlobalTheory.RSnm.detAbs (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ^ y =
      (∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-y * ∑ i, (l.1 w i : ℝ))) * GlobalTheory.RSnm.detAbs g ^ y := fun y => by
    have := GlobalTheory.CellEvalDet.detPow_tl_mul E (m + 1) ϖ hϖ l.1 y g
    rwa [GlobalTheory.CellEvalDet.detPow_eq_rpow, GlobalTheory.CellEvalDet.detPow_eq_rpow] at this
  refine ⟨?_, ?_, ?_⟩
  · set y : ℝ := x - (((m + r + 1 + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) / 2 with hy
    have hp : ∀ (z : ℝ) (h : GA E (m + 1)), ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ ((z : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2) =
        ((GlobalTheory.RSnm.detAbs h ^ (z - (((m + r + 1 + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) / 2) : ℝ) : ℂ) := fun z h => by
      rw [Complex.ofReal_cpow (GlobalTheory.RSnm.detAbs_pos h).le]
      congr 1
      push_cast
      ring
    have hg2 : GlobalTheory.RSnm.detAbs g ^ y = GlobalTheory.RSnm.detAbs g ^ ((0 : ℝ) - (((m + r + 1 + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) / 2) *
        GlobalTheory.RSnm.detAbs g ^ x := by
      rw [← Real.rpow_add (GlobalTheory.RSnm.detAbs_pos g), hy]
      congr 1
      ring
    have key : ((GlobalTheory.CellDec.dinv (m + 1) l.1 : ℝ) : ℂ) *
        ((∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat fun i => (l.1 w i).toNat)) *
          conj (∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (fun i => (l.1 w i).toNat))) *
        (((∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-y * ∑ i, (l.1 w i : ℝ))) : ℝ) : ℂ) =
        l.1.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
          (fun i => (β w i : ℂ)) x v := by
      rw [map_prod, ← Finset.prod_mul_distrib, GlobalTheory.CellDec.dinv, Complex.ofReal_prod, Complex.ofReal_prod,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finsupp.prod]
      exact Finset.prod_congr rfl fun w _ =>
        localTerm_mixed (qV E w) (hq w) hmn _ _ x y hy (l.1 w) (hgood w).1 (hgood w).2
    have hcc : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
    rw [GlobalTheory.RSnmUnf.uIntNM, GlobalTheory.RSnmUnf.uIntNM, hp, hp, ← hy, hdet, hg2, e1, e2, e3, ← key, map_mul, map_mul,
      Complex.ofReal_mul, Complex.ofReal_mul]
    generalize GlobalTheory.JSW.whit φ (blockGL hmn g) = W₁
    generalize conj (GlobalTheory.JSW.whit φ' g) = W₂
    linear_combination (exp := 1) (((GlobalTheory.CellDec.dinv (m + 1) l.1 : ℝ) : ℂ) *
        ((∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat fun i => (l.1 w i).toNat)) *
          conj (∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (fun i => (l.1 w i).toNat))) *
        (((∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-y * ∑ i, (l.1 w i : ℝ))) : ℝ) : ℂ) * W₁ * W₂ *
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g) *
        ((GlobalTheory.RSnm.detAbs g ^ ((0 : ℝ) - (((m + r + 1 + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) / 2) : ℝ) : ℂ) *
        ((GlobalTheory.RSnm.detAbs g ^ x : ℝ) : ℂ)) * hcc
  · rw [e1, e3, hdet, GlobalTheory.CellDec.dinv, Finsupp.prod, Finset.prod_congr rfl fun w _ => if_pos (hgood w)]
    refine ennreal_collect _ _ _ _ _ (fun w => zpow_nonneg (Nat.cast_nonneg _) _)
      (fun w => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun w _ => ?_) c _ hc _ _
    exact localTerm_diag (qV E w) (hq w) hmn _ x _ (by push_cast; ring) (l.1 w) (hgood w).1 (hgood w).2
  · rw [e2, e3, hdet, GlobalTheory.CellDec.dinv, Finsupp.prod, Finset.prod_congr rfl fun w _ => if_pos (hgood w)]
    refine ennreal_collect _ _ _ _ _ (fun w => zpow_nonneg (Nat.cast_nonneg _) _)
      (fun w => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun w _ => ?_) c _ hc _ _
    have := localTerm_diag (qV E w) (hq w) le_rfl (fun i => (β w i : ℂ)) x x (by ring) (l.1 w) (hgood w).1 (hgood w).2
    rw [padNat_self] at this
    rw [padNat_self]
    exact this
end
end

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section
namespace GlobalTheory.RSCellEul

open GlobalTheory.RSnmEul GlobalTheory.RSnmUnf

theorem term_le_locFac {m k : ℕ} (h : m + 1 ≤ k) (q : ℕ) (a : Fin k → ℂ) (x : ℝ) (v : Fin (m + 1) → ℤ) :
    (if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≤
      GlobalTheory.RSCell.locFac q a x (padInt h v) := by
  split_ifs with hv
  · have hv' := padInt_valid h hv
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hv'.2, hv'.1⟩, toNat_padInt h v, sum_padNat h]
  · exact bot_le

theorem term_zero {m k : ℕ} (q : ℕ) (a : Fin k → ℂ) (x : ℝ) :
    (if (∀ i, 0 ≤ (0 : Fin (m + 1) → ℤ) i) ∧ Antitone (0 : Fin (m + 1) → ℤ) then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => ((0 : Fin (m + 1) → ℤ) i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, ((0 : Fin (m + 1) → ℤ) i).toNat : ℕ) : ℝ) * x))) else 0) = 1 := by
  have h0 : (fun i : Fin (m + 1) => ((0 : Fin (m + 1) → ℤ) i).toNat) = 0 := funext fun _ => rfl
  rw [if_pos ⟨fun _ => le_rfl, fun _ _ _ => le_rfl⟩, h0, padNat_zero]
  rw [show (0 : Fin k → ℕ) = fun _ => 0 from rfl, GlobalTheory.RSPole.EulerPole.schurAt_const_zero]
  simp

theorem tprod_le_of_one_le {I : Type} (f g : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    ∏' i, f i ≤ ∏' i, g i := by
  have hg : ∀ i, 1 ≤ g i := fun i => (hf i).trans (hfg i)
  rw [(GlobalTheory.RSPole.EulerPole.hasProd_of_one_le f hf).tprod_eq, (GlobalTheory.RSPole.EulerPole.hasProd_of_one_le g hg).tprod_eq]
  exact iSup_mono fun s => Finset.prod_le_prod' fun i _ => hfg i

theorem tsum_padTerm_ne_top : ∀ (E : Type) [Field E] [NumberField E] (m k : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), m + 1 ≤ k →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin k → ℂ) (x : ℝ),
    GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => α w.1 i) x ≠ ⊤ →
    ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (l.1.prod fun w v => if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
            (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≠ ⊤ := by
  intro E _ _ m k S hmk α x hfin
  classical
  let g : HeightOneSpectrum (𝓞 E) → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun w v =>
    if (∀ i, 0 ≤ v i) ∧ Antitone v then
      ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
        (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0
  show ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g ≠ ⊤
  have hg0 : ∀ w, g w 0 = 1 := fun w => term_zero _ _ _
  obtain ⟨e, he⟩ := GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  let f : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun i v => g i.1 v
  have h1 : ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g = ∑' l' : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l'.prod f := by
    rw [← e.tsum_eq]; exact tsum_congr fun l => (he ℝ≥0∞ g hg0 l).symm
  rw [h1, (GlobalTheory.EulerSum.euler_product_intVec_ennreal (m + 1) f fun i => hg0 i.1).2]
  refine ne_top_of_le_ne_top hfin ?_
  rw [GlobalTheory.RSPole.eulD]
  refine tprod_le_of_one_le _ _ (fun i => ?_) (fun i => ?_)
  · exact le_of_eq_of_le (hg0 i.1).symm (ENNReal.le_tsum (f := f i) 0)
  · rw [GlobalTheory.RSCellSum.schurDir_eq_tsum_locFac]
    calc ∑' v, f i v ≤ ∑' v, GlobalTheory.RSCell.locFac (Ideal.absNorm i.1.asIdeal) (α i.1) x (padInt hmk v) :=
          ENNReal.tsum_le_tsum fun v => term_le_locFac hmk _ _ _ v
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (padInt_injective hmk) _

end GlobalTheory.RSCellEul
end
end

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.RSnmCells

theorem rsTermNM_zero (q : ℕ) {n m : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) :
    GlobalTheory.RSnmUnf.rsTermNM q α β x 0 = 1 := by
  have h1 : (GlobalTheory.RSnmUnf.padNat (n := n) fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0 := by
    funext i; simp [GlobalTheory.RSnmUnf.padNat]
  have h2 : (fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0 := by funext i; simp
  rw [GlobalTheory.RSnmUnf.rsTermNM, if_pos ⟨fun i => le_rfl, antitone_const⟩, h1, h2]
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

theorem unfolded_cells_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (m + r + 1 + 1), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
      (∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
      Continuous κ → (∀ h, 0 ≤ κ h) → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ h, κ (u * h) = κ h) →
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) →
      (∃ h₀ ∈ GlobalTheory.JSW.supS E (m + 1) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        ∀ x : ℝ, 1 < x →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (β w.1 i : ℂ)) x ≠ ⊤ →
          (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤) ∧ (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤) ∧
          ∫ g in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g ∂μ =
            (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) *
              ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ),
                l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ))
                  (fun i => (β w.1 i : ℂ)) x v := by
  intro E _ _ _ m r S hψ π π' hπ hπ' α β φ φ' κ hφ hφ' hU hK hU' hK' hshβ hshα hmatch hκc hκ0 hκN hκC hκU h₀
  classical
  have hϖex : ∀ w : HeightOneSpectrum (𝓞 E), ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E) := by
    intro w
    obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, IsUnifV E w ϖ := ⟨_, Formalism.L2.Host.unif_spec w⟩
    refine ⟨Units.mk0 ϖ fun h => ?_, hϖ⟩
    rw [IsUnifV, h] at hϖ
    simp at hϖ
  choose ϖ hϖ using hϖex
  have hreg : ∀ {a : ℕ} {ρ : CuspSub E a}, ρ.IsUnitary → ∀ F ∈ GlobalTheory.JSW.mspanR ρ, GlobalTheory.JSW.IsBCC F := by
    intro a ρ hρ F hF
    obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hρ F hF
    have h0 := (h []).2
    rwa [GlobalTheory.JSW.word_nil] at h0
  have hc := hreg hπ φ hφ
  have hc' := hreg hπ' φ' hφ'
  have hW : ∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc.cont (fun γ g => hc.left γ g) hu g
  have hW' : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc'.cont (fun γ g => hc'.left γ g) hu g
  have hWc := GlobalTheory.JSW.WhitCont.continuous_whit E _ φ hc.cont hc.bdd
  have hWc' := GlobalTheory.JSW.WhitCont.continuous_whit E _ φ' hc'.cont hc'.bdd
  have hRI : ∀ {a : ℕ} (Φ : GA E a → ℂ), (∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧
        ∀ u ∈ U, ∀ g, Φ (g * finGL E a u) = Φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w a, ∀ g, Φ (g * finGL E a (locGL E a w k)) = Φ g) →
      ∀ k : GL (Fin a) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v a) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit Φ (g * finGL E a k) = GlobalTheory.JSW.whit Φ g := by
    intro a Φ ⟨U, hUo, hUi⟩ hKi k hk1 hk2 g
    let stab : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | ∀ g, Φ (g * finGL E a k) = Φ g}
        mul_mem' := fun {a' c} ha hc g => by rw [map_mul, ← mul_assoc, hc, ha]
        one_mem' := fun g => by rw [map_one, mul_one]
        inv_mem' := fun {a'} ha g => by
          rw [← ha (g * finGL E a a'⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] }
    let V : Subgroup (GL (Fin a) (Af E)) := U ⊔ Subgroup.closure
      {k | ∃ w ∉ S, ∃ k' ∈ KGL w a, locGL E a w k' = k}
    have hVle : V ≤ stab := by
      refine sup_le (fun k hk => hUi k hk) (Subgroup.closure_le _ |>.2 ?_)
      rintro _ ⟨w, hw, k, hk, rfl⟩
      exact hKi w hw k hk
    have hVo : IsOpen (V : Set (GL (Fin a) (Af E))) := Subgroup.isOpen_mono (le_sup_left : U ≤ V) hUo
    have hVK : ∀ w ∉ S, ∀ k ∈ KGL w a, locGL E a w k ∈ V := fun w hw k hk =>
      (le_sup_right : Subgroup.closure _ ≤ V) (Subgroup.subset_closure ⟨w, hw, k, hk, rfl⟩)
    obtain ⟨J, -, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hVo hVK
    have hkJ : k ∈ GlobalTheory.RSLocalPart.levelAt a S J := by
      refine ⟨hk1, fun v hv i j => ?_⟩
      have e1 := congrArg (fun M : GL (Fin a) (v.adicCompletion E) => (M : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (hk2 v hv)
      have e2 : ((k.val - 1) i j) v = 0 := by
        have e1' : pLoc E v (k.val i j) = (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j := by simpa using e1
        change pLoc E v (k.val i j - (1 : Matrix (Fin a) (Fin a) (Af E)) i j) = 0
        rw [map_sub, e1', Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e2, map_zero]
      exact zero_le'
    have e : (fun z => Φ (z * finGL E a k)) = Φ := funext fun z => hVle (hJV hkJ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hWK := hRI φ hU hK
  have hWK' := hRI φ' hU' hK'
  obtain ⟨h₀, hh₀, hκ₀, hW₀⟩ := h₀
  have hint : ∀ w ∉ S, ∀ j, pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) ∈ w.adicCompletionIntegers E := by
    intro w hw j
    have e1 := congrArg (fun M : GL (Fin (m + 1)) (w.adicCompletion E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) (hh₀ w hw)
    have e2 : pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j := by
      simpa [GlobalTheory.ZEul.lastRow] using e1
    rw [e2, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨F, hFSB, hFc, hFr, hFpos, hFsc⟩ := GlobalTheory.FourierCell.exists_fourier_gauss_lattice E m S (GlobalTheory.ZEul.lastRow h₀) hint
  refine ⟨F, hFSB, ?_⟩
  intro μ _ 𝓕₀ h𝓕
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hfC, hfu, hdet, hDA, hDB⟩ := GlobalTheory.T.rankinSelberg_cell_integral_finite_part_nonneg E m r S φ φ' κ F hWc hWc' hW hW'
    hWK hWK' hmatch hκc hκ0 hκC ⟨h₀, hh₀, hκ₀, hW₀, hFpos⟩ hFc hFr μ 𝓕₀ h𝓕
  refine ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, ?_⟩
  intro x hx hdα hdβ

  have ev := GlobalTheory.CellEvalNM.uIntNM_cell_eval E m r S hψ ϖ hϖ α β φ φ' F hW hW' hWK hWK' (hshβ ϖ hϖ) (hshα ϖ hϖ)
    (fun a ha y hy => hFsc ϖ hϖ a ha y hy) x
  obtain ⟨hWbc, hFlc, hmeas, hinv, hbd⟩ := GlobalTheory.RSnmUnfProps.uIntNM_props E m r S φ φ' F hWc hWc' hW hW' hFc
  have hC0 : MeasurableSet (GlobalTheory.CellDec.C0 E (m + 1) S) := (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S).measurableSet
  set I : ℂ := ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ with hI
  have hIC : ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (f g : ℂ) * Complex.exp (x * t g) ∂μ = I := by
    rw [hI, Set.inter_comm, ← Measure.restrict_restrict hC0, ← integral_indicator hC0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg]; simp [hfC g hg]
  have hs : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ :=
    h𝓕.nullMeasurableSet.inter hC0.nullMeasurableSet

  have hlinD : ∀ (D : GA E (m + 1) → ℝ≥0∞) (c : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℝ≥0∞), Measurable D →
      (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, D (u * g) = D g) →
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        D (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) = c l * D g) →
      ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D g ∂μ ≠ ⊤ → (∑' l, c l) ≠ ⊤ → ∫⁻ g in 𝓕₀, D g ∂μ ≠ ⊤ := by
    intro D c hDm hDi hDc hD hc
    rw [GlobalTheory.CellDec.cell_lintegral μ S ϖ hϖ 𝓕₀ h𝓕 D hDm hDi]
    have : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
        c l * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D g ∂μ := by
      intro l
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← lintegral_const_mul'' _ hDm.aemeasurable]
      exact lintegral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => hDc g hg.2 l)
    simp_rw [this, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hc hD
  have hen : ∀ {a b : ℂ}, ‖a‖ = ‖b‖ → ‖a‖ₑ = ‖b‖ₑ := fun h => by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h]
  have hmD : ∀ s : ℝ, Measurable fun g : GA E (m + 1) =>
      ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ₑ ^ 2 *
        ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s) :=
    fun s => ((hWbc.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))
  have hmD' : ∀ s : ℝ, Measurable fun g : GA E (m + 1) =>
      ‖GlobalTheory.JSW.whit φ' g‖ₑ ^ 2 *
        ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s) :=
    fun s => ((hWc'.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))
  have LA := hlinD _ _ (hmD _) (fun u hu g => by
      obtain ⟨h1, -, h3, h4, -⟩ := hinv u hu g
      rw [hen h1, h3, h4]) (fun g hg l => (ev g hg l).2.1) (hDA x)
    (GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + r + 1 + 1) S (by omega) (fun w i => (α w i : ℂ)) x hdα)
  have LB := hlinD _ _ (hmD' _) (fun u hu g => by
      obtain ⟨-, h2, h3, h4, -⟩ := hinv u hu g
      rw [hen h2, h3, h4]) (fun g hg l => (ev g hg l).2.2) (hDB π' hπ' hφ' hFSB x hx)
    (GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + 1) S le_rfl (fun w i => (β w i : ℂ)) x hdβ)
  refine ⟨LA, LB, ?_⟩

  have hDtr : ∀ (a b : ℂ) (s : ℝ) (g : GA E (m + 1)), (‖a‖ₑ ^ 2 * ‖b‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s)).toReal =
      ‖a‖ ^ 2 * ‖b‖ * GlobalTheory.RSnm.detAbs g ^ s := by
    intro a b s g
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, toReal_enorm,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (GlobalTheory.RSnm.detAbs_pos g).le _)]
  have iA := integrable_toReal_of_lintegral_ne_top (hmD (x - ((r : ℝ) + 1))).aemeasurable LA
  have iB := integrable_toReal_of_lintegral_ne_top (hmD' x).aemeasurable LB
  have i12 : Integrable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) (μ.restrict 𝓕₀) :=
    Integrable.mono' ((iA.add iB).div_const 2) (hmeas x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        simp only [Pi.add_apply, hDtr]
        exact hbd x g)
  have hl : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
      ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S,
        GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
      (l.1.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (β w i : ℂ)) x v) * I := by
    intro l
    rw [← integral_const_mul, ← hIC, ← integral_const_mul]
    refine integral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => ?_)
    dsimp only
    rw [(ev g hg.2 l).1, hfu g hg.2, hdet, mul_assoc]
  have h := (GlobalTheory.CellDec.cell_integral μ S ϖ hϖ 𝓕₀ h𝓕 _ (hmeas x) i12 (fun u hu g => (hinv u hu g).2.2.2.2 x)).2
  simp_rw [hl] at h
  rw [← h.tsum_eq, tsum_mul_right, mul_comm]
  obtain ⟨e, he⟩ := GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  congr 1
  rw [← e.tsum_eq]
  exact tsum_congr fun l => (he ℂ (fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
    (fun i => (β w i : ℂ)) x v) (fun i => rsTermNM_zero _ _ _ _) l).symm

end GlobalTheory.RSnmCells
end

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolded_rankinSelberg_cellIntegral_matchedVectors : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (m + r + 1 + 1), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
      (∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
      Continuous κ → (∀ h, 0 ≤ κ h) → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ h, κ (u * h) = κ h) →
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) →
      (∃ h₀ ∈ GlobalTheory.JSW.supS E (m + 1) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        ∀ x : ℝ, 1 < x →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (β w.1 i : ℂ)) x ≠ ⊤ →
          (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤) ∧ (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤) ∧
          ∫ g in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g ∂μ =
            (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) *
              ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ),
                l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ))
                  (fun i => (β w.1 i : ℂ)) x v := by
  first | (exact @GlobalTheory.RSnmCells.unfolded_cells_eq) | (exact GlobalTheory.RSnmCells.unfolded_cells_eq) | (intros; apply GlobalTheory.RSnmCells.unfolded_cells_eq  <;> assumption)
end
