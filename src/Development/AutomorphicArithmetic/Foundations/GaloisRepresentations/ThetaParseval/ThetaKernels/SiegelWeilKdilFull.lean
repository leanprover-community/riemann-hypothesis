import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.GIdilFull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.DecompW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilSteps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Assembly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilTheta
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.SplitDomOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilTbBdd
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDone
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocTop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocFamPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopMChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocNbar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.WeightFactorEqAutomorphy
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockGood

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem gIdil_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hTP : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaPt_k) (hFP : FPSw) (hMC : MatCount)
    (hSD : _root_.PositivityTheory.SiegelWeilFormula.Kdil.SplitDom_k) (hTB : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaBdd_k) (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) (hBD : BigDense) (hHM : HolMean)
    (hDC : DerCont) (hSO : StripOK) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k := by
  intro F E _ _ _ _ _ σ d R w Ψ hΨ φ hφ g X a ha
  obtain ⟨-, -, -, -, hTA⟩ := hT
  obtain ⟨hμ0, hμT, hTA'⟩ := hTA F E σ d
  obtain ⟨-, -, hGtop, -, -, -⟩ := hAux F E σ d
  obtain ⟨L, hL⟩ := hLE F E σ d R w
  obtain ⟨y₀, Ψ', hrep, hmaj⟩ := hSD F E σ d R w L hL Ψ hΨ g
  obtain ⟨Gf, hreal, hhol, hcont, hbd, hder⟩ := hLF F E σ d R w L hL X a ha
  obtain ⟨hUo, hUR, hUb⟩ := hSO d.n X
  have hcount := hMC E d.m d.n
  set U := strip X with hU
  have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0
  set Fm : GR d.n → ℂ → UA σ d.A.J → Matrix (Fin d.m) (Fin d.n) E → ℂ := fun y z h Xr =>
    Gf (y₀ * y) z (R.loc w (mat h⁻¹ * incM F Xr)) * Ψ' (mat h⁻¹ * incM F Xr) with hFm
  set ν : Measure (UA σ d.A.J) := (d.μ.restrict d.D Set.univ)⁻¹ • d.μ.restrict d.D with hν
  have hav : ∀ f : UA σ d.A.J → ℂ, (⨍ h in d.D, f h ∂d.μ) = ∫ h, f h ∂ν := fun f => rfl
  have hc : (d.μ.restrict d.D Set.univ)⁻¹ ≠ ⊤ := by
    rw [ENNReal.inv_ne_top, Measure.restrict_apply_univ]; exact hμ0
  haveI : IsFiniteMeasure (d.μ.restrict d.D) := isFiniteMeasure_restrict.mpr hμT
  have hI : ∀ Φ ∈ d.sch, ∀ x, d.I Φ x =
      ∫ h, ∑' Xr : Matrix (Fin d.m) (Fin d.n) E, d.T (d.om x Φ) (mat h⁻¹ * incM F Xr) ∂ν := by
    intro Φ hΦ x
    rw [← hav]
    show (⨍ h in d.D, thetaSum F (d.om x (d.S h Φ)) ∂d.μ) = _
    simp_rw [hTP F E σ d Φ hΦ x]
  have hT1 : ∀ P y', d.T (d.om (g * R.ι w y') (φ P)) = R.tens w (L (y₀ * y') (fP P)) Ψ' := fun P y' =>
    hrep (φ P) (hφ P).1 (fP P) (hFP _ _ P) (hφ P).2 y'
  obtain ⟨hHc, hHd, hHr⟩ := hHM (GR d.n) (UA σ d.A.J) (Matrix (Fin d.m) (Fin d.n) E) ν U hUo hUb Fm
    (fun p h Xr => (hhol (y₀ * p) _).mul_const _)
    (fun h Xr => ((hcont (R.loc w (mat h⁻¹ * incM F Xr))).comp (f := fun q : GR d.n × ℂ => (y₀ * q.1, q.2))
      (by fun_prop) (fun q hq => ⟨trivial, hq.2⟩)).mul continuousOn_const)
    (by
      intro p t _
      have e : (fun h => ∑' k, Fm p t h k) = fun h => thetaSum F (d.om (g * R.ι w (p * a t)) (d.S h (φ 1))) := by
        funext h
        rw [hTP F E σ d (φ 1) (hφ 1).1, hT1 1 (p * a t)]
        simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hreal, mul_assoc]
      rw [e]
      exact ((hTA' (φ 1) (hφ 1).1).1 _).aestronglyMeasurable.smul_measure _)
    (by
      rintro ⟨p, z⟩ ⟨-, hz⟩
      obtain ⟨N, hN, C, δ, hδ, hCb⟩ := hbd (y₀ * p, z) ⟨trivial, hz⟩
      obtain ⟨K, hK⟩ := hTB F E σ d _ (hmaj δ hδ)
      refine ⟨(fun q : GR d.n × ℂ => (y₀ * q.1, q.2)) ⁻¹' N,
        (Continuous.continuousAt (by fun_prop)).preimage_mem_nhds hN,
        fun h Xr => |C| * ‖R.tens w (fun u => (Real.exp (-δ * sq u) : ℂ)) Ψ' (mat h⁻¹ * incM F Xr)‖,
        fun _ => |C| * K, fun h => (hK h).1.mul_left _, (integrable_const _).smul_measure hc, ?_, ?_⟩
      · intro h
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hK h).2 (abs_nonneg C)
      · intro q' hq' hq'U h Xr
        have hb1 := hCb (y₀ * q'.1, q'.2) hq' hq'U (R.loc w (mat h⁻¹ * incM F Xr))
        have he : 0 ≤ Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr))) := (Real.exp_pos _).le
        simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
        calc ‖Gf (y₀ * q'.1) q'.2 (R.loc w (mat h⁻¹ * incM F Xr))‖ * ‖Ψ' (mat h⁻¹ * incM F Xr)‖
            ≤ (C * Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr)))) * ‖Ψ' (mat h⁻¹ * incM F Xr)‖ :=
              mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
          _ ≤ (|C| * Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr)))) * ‖Ψ' (mat h⁻¹ * incM F Xr)‖ := by
              gcongr; exact le_abs_self C
          _ = _ := by ring)
  clear_value Fm
  refine ⟨U, fun y z => ∫ h, ∑' k, Fm y z h k ∂ν, hUo, hUR, hHc, fun y => ⟨hHd y, ?_, ?_⟩⟩
  · intro t
    beta_reduce
    rw [hI (φ 1) (hφ 1).1, hT1 1 (y * a t)]
    congr 1
    funext h
    congr 1
    funext Xr
    simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hreal, mul_assoc]
  · intro r
    have key : ∀ y', ((mR (y₀ * y')).toBlocks₂₂).det ≠ 0 →
        iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 =
          d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') := by
      intro y' hy'
      rw [hHr y' 0 h0U r, hI _ (hφ _).1, hT1]
      congr 1
      funext h
      congr 1
      funext Xr
      simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
      rw [iteratedDeriv_mul_const' (fun z => Gf (y₀ * y') z (R.loc w (mat h⁻¹ * incM F Xr))) _ r]
      beta_reduce
      rw [hder (y₀ * y') hy' r]
    have hDC' := hDC (GR d.n) U hUo (fun y' z => ∫ h, ∑' k, Fm y' z h k ∂ν) hHc hHd r
    have hpair : Continuous fun y' : GR d.n => (y', (0 : ℂ)) := by fun_prop
    have hcL : Continuous fun y' => iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 :=
      hDC'.comp_continuous hpair (fun _ => ⟨trivial, h0U⟩)
    have hcR : Continuous fun y' => d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') :=
      (hTA' _ (hφ _).1).2.1.comp (continuous_const.mul (R.cont w))
    have hden : Dense {y' : GR d.n | ((mR (y₀ * y')).toBlocks₂₂).det ≠ 0} :=
      (hBD d.n).preimage (isOpenMap_mul_left y₀)
    exact congrFun (hcL.ext_on hden hcR key) y
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem splitDom_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.Kdil.DecompW_k) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.SplitDom_k := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ g
  obtain ⟨x, y₀, hg, hx⟩ := hD F E σ d R w g
  obtain ⟨A, hA⟩ := hAw F E σ d R w x hx
  have hind : d.Indep w Ψ := ((_root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k F E σ d R).2.1 w Ψ hΨ).2
  refine ⟨y₀, A Ψ, ?_, ?_⟩
  · intro Φ hΦ f hf hTΦ y
    obtain ⟨hLf, hLΦ⟩ := hL (y₀ * y) f hf
    have h1 := hLΦ Ψ hind Φ hΦ hTΦ
    rw [hg, mul_assoc, ← map_mul, map_mul, Module.End.mul_apply]
    exact ((hA Ψ hind).2 _ hLf _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.om_mem_k d _ hΦ) h1)
  · intro δ hδ
    obtain ⟨Φ, hΦ, hTΦ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftSw1_k hT.1 d R w _ (isSw_gauss hδ) Ψ hΨ
    rw [← (hA Ψ hind).2 _ (isSw_gauss hδ) Φ hΦ hTΦ]
    exact (hT.1 F E σ d).1 _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.om_mem_k d x hΦ)
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem decompW_k : _root_.PositivityTheory.SiegelWeilFormula.Kdil.DecompW_k := fun _ _ _ _ _ _ _ _ d R w g => _root_.PositivityTheory.SiegelWeilFormula.KSplitW.decompW_k d R w g
theorem gIdil_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hS : GlobalTheory.Published.SiegelSetUnitary)
    (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) (hBD : BigDense) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil_of_k hT hAux hLE (_root_.PositivityTheory.SiegelWeilFormula.Kdil.thetaPt_of_k hT) (fun _ _ P => KFock.isSw_fP P) matCount (_root_.PositivityTheory.SiegelWeilFormula.Kdil.splitDom_of_k hT hAw _root_.PositivityTheory.SiegelWeilFormula.Kdil.decompW_k)
    (_root_.PositivityTheory.SiegelWeilFormula.Kdil.thetaBdd_of_k hS) hLF hBD holMean derCont stripOK
theorem gIdil'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil_k hT hAux hLE hAw GlobalTheory.T.siegel_set_unitary hLF bigDense
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fam_eq_L_pf_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L)
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (s : ℝ) :
    L (a s) (fP 1) = fun v => fam d.m X s v := by
  obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
  set A : Matrix (Fin d.n) (Fin d.n) ℂ := diagonal fun j => (Real.exp (s * X j) : ℂ) with hA
  have hdet : A.det = ((Real.exp (∑ j, s * X j) : ℝ) : ℂ) := by
    rw [hA, det_diagonal, Real.exp_sum, Complex.ofReal_prod]
  have hpos : 0 < Real.exp (∑ j, s * X j) := Real.exp_pos _
  have hunit : IsUnit A.det := by
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hpos.ne')
  have hinv : (Aᴴ)⁻¹ = diagonal fun j => (Real.exp (-(s * X j)) : ℂ) := by
    rw [hA, diagonal_conjTranspose]
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hy : mR (a s) = mLoc A := by
    rw [show mR (a s) = _ from ha s, mLoc, hinv]
  rw [hk (a s) A hunit hy (fP 1) (hFP d.m d.n 1)]
  funext v
  have hn : ‖A.det‖ = Real.exp (∑ j, s * X j) := by
    rw [hdet, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  rw [hn, ← hdet, div_self hunit.ne_zero, _root_.one_zpow, one_mul, hdet]
  simp only [fam, fP, evX, map_one, one_mul, gs]
  congr 1
  · rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, Complex.ofReal_exp]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · congr 1
    push_cast
    rw [neg_mul]
    congr 2
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
    have he : (Matrix.of v * A) b j = v b j * ((Real.exp (s * X j) : ℝ) : ℂ) := by
      rw [hA, Matrix.mul_diagonal]
      rfl
    erw [he]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Complex.ofReal_mul, mul_pow,
      Complex.ofReal_exp, ← Complex.exp_nat_mul, mul_comm]
    congr 2
    push_cast
    ring
theorem fam_eq_L_closed_k : type_of% @_root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_eq_L_pf_k := @_root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_eq_L_pf_k
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
open PositivityTheory.Rg.Sw.Glob (aC ptZ jC gC actZ jF IsSiegel gZf)
open Matrix
variable {n : ℕ}
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem abs_tw_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : |2 * Real.pi * ((R.sg w : ℤ) : ℝ)| = 2 * Real.pi := by
  rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h, abs_of_pos Real.pi_pos]
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
open PositivityTheory.Rg.Sw.Glob (aC ptZ jC gC actZ jF IsSiegel gZf)
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem vac_law_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P)) (y : GR d.n) :
    L y (fP 1) = fun u => F0 p q e y *
      gZf (fun _ : Fin d.m => true) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (2 * Real.pi) (actZ y (Complex.I • 1)) u := by
  obtain ⟨pp, k, hpp, hk, rfl⟩ := PositivityTheory.Rg.Sw.AbsSt.iwa d.n y
  have hk' : InK (mR k) := hk
  obtain ⟨nb, ma, b, a, hb, ha, hnb, hma, hpe, hZ⟩ := up_decomp_closed pp hpp
  obtain ⟨c, -, hcf⟩ := R.locOp_mM hT hG hL
  have hsw1 : IsSw (fP (1 : PX d.m d.n)) := hFP d.m d.n 1
  have hk1 : L k (fP 1) = fun u => F0 p q e k * fP 1 u := by
    rw [hρ k 1 hk', hLD.kvac k hk', fP_smul_one]
  have hma21 : (mR ma).toBlocks₂₁ = 0 := by rw [hma, mLoc, Matrix.toBlocks_fromBlocks₂₁]
  have hnb21 : (mR nb).toBlocks₂₁ = 0 := by rw [hnb, nU, Matrix.toBlocks_fromBlocks₂₁]
  have hca : c a = F0 p q e ma := by
    have h1 := hLD.law 1 ma 1 hma21
    have h0 : fP (1 : PX d.m d.n) (Matrix.of (0 : Fin d.m → Fin d.n → ℂ) * a) = 1 := by
      have e0 : (Matrix.of (0 : Fin d.m → Fin d.n → ℂ) * a : Matrix (Fin d.m) (Fin d.n) ℂ) = 0 := by
        ext i j; simp [Matrix.mul_apply]
      rw [e0]; exact fP_one_zero
    rw [mul_one, hsL, hsL, hcf ma a ha hma _ hsw1, R.locOp_one hT hG hL _ hsw1] at h1
    beta_reduce at h1
    rw [fP_one_of _ (fun i j => by
      show ∑ k, (Matrix.of (0 : Fin d.m → Fin d.n → ℂ)) i k * a k j = 0
      simp), fP_one_zero] at h1
    simpa using h1
  have hF0 : F0 p q e (pp * k) = c a * F0 p q e k := by
    have m1 := ((PositivityTheory.Rg.Sw.AbsSt.mult d.n p q e).2 pp k hpp).1
    have m2 := ((PositivityTheory.Rg.Sw.AbsSt.mult d.n p q e).2 nb ma hnb21).1
    rw [m1, hpe, m2, weight_factor_unipotent_one p q e nb b hnb, one_mul, hca]
  have hZ' : actZ (pp * k) (Complex.I • 1) = b + Complex.I • (a * aᴴ) := by rw [actZ_mul_K pp k hk', hZ]
  have hswk : IsSw (L k (fP 1)) := (hL k _ hsw1).1
  have hswm : IsSw (L ma (L k (fP 1))) := (hL ma _ hswk).1
  rw [R.locOp_mul hT hG hL pp k _ hsw1, hpe, R.locOp_mul hT hG hL nb ma _ hswk, R.locOp_nU hT hG hL nb b hb hnb _ hswm,
    hcf ma a ha hma _ hswk, ← hpe, hF0, hZ', hk1]
  funext u
  rw [gzf_eval (R.sg w) b a hb u]
  ring_nf
  rfl
theorem gf_L_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (s : ℝ) :
    Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X y s = L (y * a s) (fP 1) := by
  rw [gf_real e p q _ X a ha y s, _root_.PositivityTheory.SiegelWeilFormula.Kdil.vac_law_k R hT hG hFP hL hLD hsL hρ (y * a s)]
theorem fam_sw_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L)
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (s : ℝ) :
    IsSw (fun v => fam d.m X s v) := by
  rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_eq_L_closed_k R hT hG hFP hL X a ha s]
  exact (hL (a s) (fP 1) (hFP _ _ 1)).1
theorem gf_L_fam_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (s : ℝ) :
    Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X y s = L y (fun v => fam d.m X s v) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Kdil.gf_L_k R hT hG hFP hL hLD hsL hρ X a ha y s, R.locOp_mul hT hG hL y (a s) (fP 1) (hFP _ _ 1),
    _root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_eq_L_closed_k R hT hG hFP hL X a ha s]
theorem der_nbar_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L) (hB : GfBound)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s))
    (nbb : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ) (hc : cᴴ = c) (hnbb : mR nbb = nbLoc c) (r : ℕ) :
    (fun v => iteratedDeriv r (fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X nbb z v) 0) =
      L nbb (fP ((dil (2 * Real.pi) X ^ r) 1)) := by
  obtain ⟨C, s', κ, ε, hs', hκ, h4, -, hconj, -, -⟩ := R.locOp_nbar hT hA hG hL
  obtain ⟨hhol, hcont, hbd⟩ := hB d.m d.n e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (_root_.PositivityTheory.SiegelWeilFormula.Kdil.abs_tw_k R w)
  have h0s : (0 : ℂ) ∈ strip X := fun j => by simp [Real.pi_pos]
  obtain ⟨N, δ, Cb, hN, hδ, hNb⟩ := hbd nbb 0 h0s
  obtain ⟨ρs, hρs, hss⟩ := strip_ball X
  have hev : (fun z : ℂ => (nbb, z)) ⁻¹' N ∈ 𝓝 (0 : ℂ) :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hN
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.mem_nhds_iff.1 hev
  set rr := min ρ0 ρs with hrrdef
  have hrr : 0 < rr := lt_min hρ0 hρs
  have hsub : Metric.ball (0 : ℂ) rr ⊆ strip X := (Metric.ball_subset_ball (min_le_right _ _)).trans hss
  have hsubN : ∀ z ∈ Metric.ball (0 : ℂ) rr, (nbb, z) ∈ N := fun z hz =>
    hball (Metric.ball_subset_ball (min_le_left _ _) hz)
  set Φ : ℂ → (Fin d.m → Fin d.n → ℂ) → ℂ := fun z v => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb z v with hΦ
  have hΦd : ∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 rr) := fun v => (hhol nbb v).mono hsub
  have hΦc : ContinuousOn (fun zv : ℂ × (Fin d.m → Fin d.n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 rr ×ˢ Set.univ) :=
    cont_slice _ _ hcont nbb _ fun zv hzv => ⟨Set.mem_univ _, hsub hzv.1, Set.mem_univ _⟩
  have hΦb : ∀ z ∈ Metric.ball (0 : ℂ) rr, ∀ v, ‖Φ z v‖ ≤ Cb * Real.exp (-δ * sq v) := by
    intro z hz v
    have h := hNb (nbb, z) (hsubN z hz) (hsub hz) v
    simpa [sq, neg_mul] using h
  have hC : C ≠ 0 := by
    intro hC0
    have h := congrFun (h4 _ (hFP d.m d.n 1)) 0
    simp only [locFT, hC0, zero_mul, Pi.smul_apply, smul_eq_mul, fP_one_zero, mul_one] at h
    exact hκ h.symm
  set P : PX d.m d.n := (dil (2 * Real.pi) X ^ r) 1 with hP
  have hGsw : IsSw (L nbb (fP P)) := (hL nbb _ (hFP _ _ P)).1
  obtain ⟨hGc, hGi⟩ := sw_cont_int hGsw
  obtain ⟨ρ9, hρ9, -, hr9⟩ := hol_int_closed Φ rr Cb δ hrr hδ hΦd hΦc hΦb (kerFT s' 0) (kerFT_cont s' 0) (kerFT_norm s' 0)
  obtain ⟨-, hDc, C', hDb⟩ := hr9 r
  have hDi : Integrable (fun v => iteratedDeriv r (fun z => Φ z v) 0) := by
    refine Integrable.mono' ((gauss_int_closed δ hδ).const_mul C') hDc.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    exact hDb v
  have key : ∀ ξ : Fin d.m → Fin d.n → ℂ, ∫ v, kerFT s' ξ v * iteratedDeriv r (fun z => Φ z v) 0 =
      ∫ v, kerFT s' ξ v * L nbb (fP P) v := by
    intro ξ
    obtain ⟨ρ1, hρ1, hd1, hr1⟩ := hol_int_closed Φ rr Cb δ hrr hδ hΦd hΦc hΦb (kerFT s' ξ) (kerFT_cont s' ξ) (kerFT_norm s' ξ)
    obtain ⟨ρ2, hρ2, hd2, hr2⟩ := fam_int_hol_closed d.m X (kerFT s' ξ) (kerFT_cont s' ξ) (kerFT_norm s' ξ)
    set ch : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) * ((Matrix.of ξ)ᴴ * Matrix.of ξ))) with hch
    have hreal : ∀ s : ℝ, |s| < min ρ1 ρ2 → C * (∫ v, kerFT s' ξ v * Φ s v) = ch * (C * ∫ v, kerFT s' ξ v * fam d.m X s v) := by
      intro s _
      have e1 : ∀ v, Φ s v = L nbb (fun v => fam d.m X s v) v := fun v =>
        congrFun (_root_.PositivityTheory.SiegelWeilFormula.Kdil.gf_L_fam_k R hT hG hFP hL hLD hsL hρ X a ha nbb s) v
      simp only [e1]
      exact congrFun (hconj nbb c hc hnbb _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_sw_k R hT hG hFP hL X a ha s)) ξ
    have hid := iteratedDeriv_eq_of_real_closed (f := fun z => C * ∫ v, kerFT s' ξ v * Φ z v)
      (g := fun z => ch * (C * ∫ v, kerFT s' ξ v * fam d.m X z v)) (ρ := min ρ1 ρ2) (lt_min hρ1 hρ2)
      ((hd1.mono (Metric.ball_subset_ball (min_le_left _ _))).const_mul C)
      (((hd2.mono (Metric.ball_subset_ball (min_le_right _ _))).const_mul C).const_mul ch) hreal r
    rw [iteratedDeriv_const_mul', iteratedDeriv_const_mul', iteratedDeriv_const_mul'] at hid
    beta_reduce at hid
    rw [(hr1 r).1, hr2 r] at hid
    simp only [fam_deriv_closed] at hid
    have h2 : C * ∫ v, kerFT s' ξ v * L nbb (fP P) v = ch * (C * ∫ v, kerFT s' ξ v * fP P v) :=
      congrFun (hconj nbb c hc hnbb _ (hFP _ _ P)) ξ
    exact mul_left_cancel₀ hC (hid.trans h2.symm)
  have hint : ∀ ξ : Fin d.m → Fin d.n → ℂ, ∀ g : (Fin d.m → Fin d.n → ℂ) → ℂ, Integrable g →
      Integrable (fun v => kerFT s' ξ v * g v) := fun ξ g hg =>
    MeasureTheory.Integrable.bdd_mul hg (kerFT_cont s' ξ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => kerFT_norm s' ξ v)
  have hfin := ft_uniq_closed s' hs' (fun v => iteratedDeriv r (fun z => Φ z v) 0 - L nbb (fP P) v) (hDc.sub hGc)
    (hDi.sub hGi) (fun ξ => by
      have h := key ξ
      rw [← sub_eq_zero, ← integral_sub (hint ξ _ hDi) (hint ξ _ hGi)] at h
      simpa [kerFT, mul_sub] using h)
  funext v
  exact sub_eq_zero.1 (congrFun hfin v)
theorem gf_der_big_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L) (hB : GfBound)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (hy : ((mR y).toBlocks₂₂).det ≠ 0)
    (r : ℕ) (u : Fin d.m → Fin d.n → ℂ) :
    iteratedDeriv r (fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X y z u) 0 =
      L y (fP ((dil (2 * Real.pi) X ^ r) 1)) u := by
  obtain ⟨pp, nbb, c, hpp, hc, hnbb, rfl⟩ := dcell_closed y hy
  obtain ⟨nb', ma', b', a', hb', ha', hnb', hma', hpe', -⟩ := up_decomp_closed pp hpp
  obtain ⟨cm, -, hcf⟩ := R.locOp_mM hT hG hL
  obtain ⟨hhol, -, -⟩ := hB d.m d.n e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (_root_.PositivityTheory.SiegelWeilFormula.Kdil.abs_tw_k R w)
  obtain ⟨ρs, hρs, hss⟩ := strip_ball X
  set eb : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
    Matrix.trace (b' * ((Matrix.of u)ᴴ * Matrix.of u))) with heb
  set w' : Fin d.m → Fin d.n → ℂ := fun i j => (Matrix.of u * a') i j with hw'
  have hform : ∀ f, IsSw f → L (pp * nbb) f u = eb * (cm a' * L nbb f w') := by
    intro f hf
    have h1 : IsSw (L nbb f) := (hL nbb f hf).1
    have h2 : IsSw (L ma' (L nbb f)) := (hL ma' _ h1).1
    rw [R.locOp_mul hT hG hL pp nbb f hf, hpe', R.locOp_mul hT hG hL nb' ma' _ h1,
      R.locOp_nU hT hG hL nb' b' hb' hnb' _ h2, hcf ma' a' ha' hma' _ h1]
    rfl
  have hreal : ∀ s : ℝ, |s| < ρs → Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (pp * nbb) s u =
      eb * (cm a' * Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb s w') := by
    intro s _
    rw [_root_.PositivityTheory.SiegelWeilFormula.Kdil.gf_L_fam_k R hT hG hFP hL hLD hsL hρ X a ha (pp * nbb) s, _root_.PositivityTheory.SiegelWeilFormula.Kdil.gf_L_fam_k R hT hG hFP hL hLD hsL hρ X a ha nbb s]
    exact hform _ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_sw_k R hT hG hFP hL X a ha s)
  have hid := iteratedDeriv_eq_of_real_closed
    (f := fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (pp * nbb) z u)
    (g := fun z => eb * (cm a' * Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb z w')) (ρ := ρs) hρs
    ((hhol _ u).mono hss) ((((hhol nbb w').mono hss).const_mul _).const_mul _) hreal r
  rw [hid, iteratedDeriv_const_mul', iteratedDeriv_const_mul']
  beta_reduce
  have hdn := congrFun (_root_.PositivityTheory.SiegelWeilFormula.Kdil.der_nbar_k R hT hA hG hFP hL hB hLD hsL hρ X a ha nbb c hc hnbb r) w'
  beta_reduce at hdn
  rw [hdn, hform _ (hFP _ _ _)]
theorem locFamG_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hB : GfBound) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k := by
  intro F E _ _ _ _ _ σ d R w L hL X a ha
  obtain ⟨sL, ρ, p, q, e, -, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  obtain ⟨hhol, hcont, hbd⟩ := hB d.m d.n e p q _ X (_root_.PositivityTheory.SiegelWeilFormula.Kdil.abs_tw_k R w)
  refine ⟨Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X, fun y t => _root_.PositivityTheory.SiegelWeilFormula.Kdil.gf_L_k R hT hG hFP hL hLD hsL hρ X a ha y t, hhol,
    fun u => ?_, fun q' hq' => ?_, fun y hy r u => _root_.PositivityTheory.SiegelWeilFormula.Kdil.gf_der_big_k R hT hA hG hFP hL hB hLD hsL hρ X a ha y hy r u⟩
  · exact cont_slice2 _ _ hcont u _ fun q' hq' => ⟨Set.mem_univ _, hq'.2, Set.mem_univ _⟩
  · obtain ⟨N, δ, C, hN, hδ, hNb⟩ := hbd q'.1 q'.2 hq'.2
    refine ⟨N, hN, C, δ, hδ, fun q'' hq'' hs u => ?_⟩
    have h := hNb q'' hq'' hs u
    simpa [sq, neg_mul] using h
theorem locFamG_of'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.locFamG_of_k hT hA hG hFP hLI gfBound
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem locFamG_done_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFP : FPSw) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.locFamG_of'_k hT hA _root_.PositivityTheory.SiegelWeilFormula.KFock.goodAwayEx_k hFP hLI
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem gIdil_full_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil'_k hT hAux hLE hAw (_root_.PositivityTheory.SiegelWeilFormula.Kdil.locFamG_done_k hT hAux (fun _ _ P => KFock.isSw_fP P) hLI)
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end
