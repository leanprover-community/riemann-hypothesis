module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFunctionBasic

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] in
theorem _root_.GlobalTheory.BesselFunctionBasic.JF_basic : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r), γ ∈ _root_.BranchingSupport.GG k r → (∀ F F' : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp), (∀ g ∈ _root_.BranchingSupport.GG k r, F g = F' g) → _root_.Formalism.FourierDecayAlt.B.JF D F γ = _root_.Formalism.FourierDecayAlt.B.JF D F' γ ∧ (Integrable (_root_.Formalism.FourierDecayAlt.JF.integrand D F γ) D.μSS → Integrable (_root_.Formalism.FourierDecayAlt.JF.integrand D F' γ) D.μSS)) ∧ (∀ (φ : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → ℂ) (F : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp)), (∀ p, D.inSS p → φ (_root_.Formalism.FourierDecayAlt.B.sgs p γ) = φ γ) → _root_.Formalism.FourierDecayAlt.B.JF D (fun g => φ g • F g) γ = φ γ • _root_.Formalism.FourierDecayAlt.B.JF D F γ) ∧ (∀ (ι : Type) [Fintype ι] (F : ι → _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp)), (∀ i, Integrable (_root_.Formalism.FourierDecayAlt.JF.integrand D (F i) γ) D.μSS) → _root_.Formalism.FourierDecayAlt.B.JF D (fun g => ∑ i, F i g) γ = ∑ i, _root_.Formalism.FourierDecayAlt.B.JF D (F i) γ) ∧ ∀ᵐ p ∂D.μSS, D.inSS p := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ D γ hγ
  have hJ : ∀ F : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp),
      _root_.Formalism.FourierDecayAlt.B.JF D F γ = ∫ p, _root_.Formalism.FourierDecayAlt.JF.integrand D F γ p ∂D.μSS := fun F => rfl
  have hae := _root_.Formalism.FourierDecayAlt.P.B6.ae_inSS D
  refine ⟨?_, ?_, ?_, hae⟩
  · intro F F' hF
    have heq : _root_.Formalism.FourierDecayAlt.JF.integrand D F γ =ᵐ[D.μSS] _root_.Formalism.FourierDecayAlt.JF.integrand D F' γ := by
      filter_upwards [hae] with p hp
      simp only [_root_.Formalism.FourierDecayAlt.JF.integrand, _root_.Formalism.FourierDecayAlt.P.B6.rho_eq, hF _ (_root_.Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hγ)]
    exact ⟨by rw [hJ, hJ]; exact integral_congr_ae heq, fun hi => hi.congr heq⟩
  · intro φ F hφ
    rw [hJ, hJ, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [hae] with p hp
    simp only [_root_.Formalism.FourierDecayAlt.JF.integrand, _root_.Formalism.FourierDecayAlt.P.B6.rho_eq, hφ p hp, map_smul]
    rw [smul_comm]
  · intro ι _ F hF
    simp only [hJ]
    rw [← MeasureTheory.integral_finsetSum _ (fun i _ => hF i)]
    congr 1
    funext p
    simp only [JF.integrand, P.B6.rho_eq, map_sum, Finset.smul_sum]

end GlobalTheory.BesselFunctionBasic
