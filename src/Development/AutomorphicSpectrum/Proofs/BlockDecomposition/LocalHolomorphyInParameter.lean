import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.FComb
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import GroundTheory.AutomorphicForms.GL2.InnerProductParamHolo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFourierTransformIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaRegionMeasureBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedShellFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerIwasawaGrowthBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricSumBelowThreshold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableZFOfBound

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.LFHolP

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def Jf (W' : GL (Fin 2) F → ℂ) (c : Fˣ →* ℂˣ) (s : ℂ) (k : GL (Fin 2) F) : ℂ :=
  ∫ a, W' (dg2 a 1 * k⁻¹) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F

def dk (k : GL (Fin 2) F) : ℝ := (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ)

theorem dk_pos (k : GL (Fin 2) F) : 0 < dk k := by
  unfold dk
  exact_mod_cast modulus_pos (Units.ne_zero _)

theorem continuous_dk : Continuous (dk : GL (Fin 2) F → ℝ) := by
  have hval : Continuous fun k : GL (Fin 2) F => (k : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have hmod : Continuous fun x : F => (modulus x : ℝ) := NNReal.continuous_coe.comp continuous_modulus
  have : Continuous fun k : GL (Fin 2) F => ((GeneralLinearGroup.det k : Fˣ) : F) := by
    simpa using hval.matrix_det
  exact hmod.comp this

theorem norm_mp_det (k : GL (Fin 2) F) (z : ℂ) : ‖mp (GeneralLinearGroup.det k) z‖ = dk k ^ z.re :=
  GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.norm_mp _ z

theorem continuous_mp_det (z : ℂ) : Continuous fun k : GL (Fin 2) F => mp (GeneralLinearGroup.det k) z := by
  have h : Continuous fun k : GL (Fin 2) F => ((dk k : ℝ) : ℂ) := Complex.continuous_ofReal.comp continuous_dk
  exact h.cpow continuous_const fun k => Complex.ofReal_mem_slitPlane.2 (dk_pos k)

theorem inn_bound {ψ : AddChar F Circle} (hψ : IsStd ψ) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (hΦ : Φ ∈ SB F) :
    ∃ C R : ℝ, ∀ k : GL (Fin 2) F, ‖inn ψ Φ k 1‖ * dk k ≤ C ∧ (inn ψ Φ k 1 ≠ 0 → k ∈ om R (1 : Fˣ)) := by
  obtain ⟨C, R, h⟩ := GlobalTheory.CompanionTheory.LFFour.gFour F ψ hψ Φ hΦ
  have e1 : dg (1 : Fˣ) 1 1 = (1 : GL (Fin 3) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg]
  have e2 : dg2 (1 : Fˣ) 1 = (1 : GL (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2]
  have key : ∀ k : GL (Fin 2) F, inn ψ Φ k 1 = mp (GeneralLinearGroup.det k) (-1) *
      pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) := by
    intro k
    have := GlobalTheory.CompanionTheory.LFGTorus.inn_dg ψ Φ k 1 1
    simpa [e1, e2] using this
  refine ⟨C, R, fun k => ⟨?_, fun hne => ?_⟩⟩
  · have hd := dk_pos k
    rw [key, norm_mul, norm_mp_det]
    have : dk k ^ (-1 : ℂ).re * dk k = 1 := by
      simp only [Complex.neg_re, Complex.one_re, Real.rpow_neg_one]
      exact inv_mul_cancel₀ hd.ne'
    calc _ = (dk k ^ (-1 : ℂ).re * dk k) * ‖pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)‖ := by ring
      _ ≤ C := by rw [this, one_mul]; exact (h _ _).1
  · have hp : pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) ≠ 0 := by
      intro h0
      exact hne (by rw [key, h0, mul_zero])
    obtain ⟨h1, h2⟩ := (h _ _).2 hp
    exact ⟨h1, fun j => by simpa using h2 j⟩



theorem exists_left_invariant {Φ : Matrix (Fin 2) (Fin 3) F → ℂ}
    (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ u ∈ U, ∀ X : Matrix (Fin 2) (Fin 3) F,
        Φ ((u : Matrix (Fin 2) (Fin 2) F) * X) = Φ X := by
  have hcont : Continuous fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 2) F =>
      (p.2 : Matrix (Fin 2) (Fin 2) F) * p.1 :=
    (Units.continuous_val.comp continuous_snd).matrix_mul continuous_fst
  have hlc : IsLocallyConstant fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 2) F =>
      Φ ((p.2 : Matrix (Fin 2) (Fin 2) F) * p.1) - Φ p.1 :=
    (hl.comp_continuous hcont).sub (hl.comp_continuous continuous_fst)
  have hopen := hlc.isOpen_fiber 0
  have hsub : tsupport Φ ×ˢ ({1} : Set (GL (Fin 2) F)) ⊆
      (fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 2) F =>
        Φ ((p.2 : Matrix (Fin 2) (Fin 2) F) * p.1) - Φ p.1) ⁻¹' {0} := by
    rintro ⟨X, u⟩ ⟨-, hu⟩
    obtain rfl : u = 1 := hu
    simp
  obtain ⟨A, B, -, hB, hA, h1, hAB⟩ :=
    generalized_tube_lemma hc isCompact_singleton hopen hsub
  obtain ⟨m, -, hm⟩ :=
    (GLnLocal.hasBasis_nhds_one F 2).mem_iff.1 (hB.mem_nhds (h1 rfl))
  have hfix : ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, ∀ X, Φ X ≠ 0 →
      Φ ((u : Matrix (Fin 2) (Fin 2) F) * X) = Φ X := by
    intro u hu X hX
    have : (X, u) ∈ A ×ˢ B := ⟨hA (subset_tsupport _ hX), hm hu⟩
    exact sub_eq_zero.1 (hAB this)
  refine ⟨⟨GLnLocal.congruenceSubgroup F 2 m, GLnLocal.isOpen_congruenceSubgroup F 2 m⟩,
    fun u hu X => ?_⟩
  have hu' : u ∈ GLnLocal.congruenceSubgroup F 2 m := hu
  by_cases hX : Φ X = 0
  · by_cases hY : Φ ((u : Matrix (Fin 2) (Fin 2) F) * X) = 0
    · rw [hX, hY]
    · have h := hfix u⁻¹ (inv_mem hu') _ hY
      rw [← Matrix.mul_assoc, Units.inv_mul_of_eq rfl, Matrix.one_mul] at h
      exact h.symm
  · exact hfix u hu' X hX

theorem cont_inn (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (hΦ : Φ ∈ SB F) :
    Continuous fun k : GL (Fin 2) F => inn ψ Φ k 1 := by
  obtain ⟨U, hU⟩ := exists_left_invariant hΦ.1 hΦ.2
  have hl : IsLocallyConstant fun g : GL (Fin 2) F => inn ψ Φ g⁻¹ 1 := by
    refine GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant _ U.toSubgroup U.isOpen fun g u hu => ?_
    have hu' : u⁻¹ ∈ U := inv_mem hu
    simp only [inn, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, hU _ hu']
  have := hl.continuous.comp (continuous_inv (G := GL (Fin 2) F))
  simpa [Function.comp_def] using this






end GlobalTheory.CompanionTheory.LFHolP
