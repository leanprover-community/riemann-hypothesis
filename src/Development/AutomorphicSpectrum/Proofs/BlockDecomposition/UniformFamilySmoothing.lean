module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

theorem continuous_sm_uFam {K : Type} [Field K] [NumberField K] {n : ℕ}
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {β : archGroup K n → ℝ} (hβ : Ker ν β) {f : AdelicGLn.AdelicGL K n → ℂ}
    (hf : Continuous f) : Continuous (sm ν β f) := by
  have hF : Continuous (Function.uncurry fun (x : AdelicGLn.AdelicGL K n) (y : archGroup K n) =>
      (β y : ℂ) * f (x * infEmb K n y)) := by
    refine (Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul (hf.comp ?_)
    exact continuous_fst.mul (continuous_infEmb.comp continuous_snd)
  set_option synthInstance.maxHeartbeats 1000000 in
  have h := continuous_parametric_integral_of_continuous (μ := ν) hF hβ.cpt.isCompact
  refine h.congr fun x => ?_
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  have : β y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [this]

theorem uFam_sm : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ)
    (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ), Ker ν β → UFam f → UFam (fun i => sm ν β (f i)) := by
  intro K _ _ n _ _ ν _ β ι f hβ hf
  refine ⟨fun i => continuous_sm_uFam ν hβ (hf.cont i), fun i γ x => ?_, ?_⟩
  · simp only [sm, mul_assoc]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hf.left i γ (x * infEmb K n y)]
  · obtain ⟨U, hU, hlev⟩ := hf.level
    refine ⟨U, hU, fun i g u => ?_⟩
    simp only [sm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [mul_assoc g, ← infEmb_mul_finEmb_comm, ← mul_assoc, hlev i (g * infEmb K n y) u]

end GlobalTheory.CompanionTheory.Conc

end
