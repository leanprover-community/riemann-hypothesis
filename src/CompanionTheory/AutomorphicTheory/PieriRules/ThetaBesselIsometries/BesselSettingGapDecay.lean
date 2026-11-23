module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBoundDualStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapBoundStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSumStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapConditionStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FactorisationOfConjHomogeneousAndHomogeneousStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselOrbital

theorem bessel_integral_eq_smul : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  classical
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hok hl hl'
  have hpt : ∀ γ ∈ JF.Om k r D.z D.z', ∃ O : Wq →L[ℂ] Wp, ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ X : Wq →L[ℂ] Wp,
      B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ = ⟪l x, X (l' y)⟫_ℂ • O := by
    intro γ hγ
    obtain ⟨A, hA1, hA2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨Bb, hB1, hB2⟩ := GlobalTheory.T.bessel_orbital_integral_factors_through_right_functional hH k r ε mu h R Wp Wq D l l' hDS hgap hok hl hl' γ hγ
    obtain ⟨O, hO⟩ := GlobalTheory.T.factorisation_of_conjHomogeneous_and_homogeneous R.TK Wp Wq (fun x => l x) (fun y => l' y)
      (fun x y X => B.JF D (fun g => ⟪(x : R.H), R.σ g y⟫_ℂ • X) γ)
      (fun y => A y) (fun x => Bb x) (fun y => hA1 y) (fun x => hB1 x)
      (fun x y X c => hA2 x x.2 y y.2 X c) (fun x y X c => hB2 x x.2 y y.2 X c)
    exact ⟨O, fun x hx y hy X => hO ⟨x, hx⟩ ⟨y, hy⟩ X⟩
  choose! OO hOO using hpt
  have hint : ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z',
      Integrable (JF.integrand D F γ) D.μSS := by
    intro F s hF γ hγ
    exact (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ F (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hok).1
      ((GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH k r ε mu h R Wp Wq l l' F s hDS hgap hok hF).2 0)).1 γ hγ
  refine ⟨OO, fun F s hF γ hγ => ⟨hint F s hF γ hγ, ?_⟩⟩
  obtain ⟨m, x, y, X, hxy, hFe, hs⟩ := hF
  have hγG : γ ∈ GG k r := hγ.1
  obtain ⟨hloc, -, hsum, -⟩ := GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum k r Wp Wq D γ hγG
  rw [(hloc F (fun g => ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i) hFe).1,
    hsum (Fin m) (fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i) ?_, hs, Finset.sum_smul]
  · exact Finset.sum_congr rfl fun i _ => hOO γ hγ _ (hxy i).1 _ (hxy i).2 _
  · intro i
    refine hint _ ⟪l (x i), X i (l' (y i))⟫_ℂ ⟨1, fun _ => x i, fun _ => y i, fun _ => X i,
      fun _ => hxy i, fun g _ => ?_, ?_⟩ γ hγ
    · simp
    · simp

end GlobalTheory.BesselOrbital
