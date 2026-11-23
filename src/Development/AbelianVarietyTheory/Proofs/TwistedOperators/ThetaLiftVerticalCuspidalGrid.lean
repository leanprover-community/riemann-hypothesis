module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspApproxX

open GlobalTheory.Grow GlobalTheory.Size

theorem thetaKO_le_quotHeight {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) {C : Set (GA D V)}
    (hC : IsCompact C) : ∃ (K : ℝ) (a : ℕ), ∀ g ∈ C, ∀ h, ‖thetaKO ω g h f‖ ≤ K * quotHeight W h ^ a := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨c, hc0, hc⟩ := (H V W rfl rfl).real ψ hθ hU
  obtain ⟨B, hB⟩ := exists_height_le_of_isCompact V hC
  have key := (hc χS χT ω hω μ 𝓕 hμ f hl).2
  set s := (sobO ψ θ μ 𝓕 d f).toReal
  have hs : 0 ≤ s := ENNReal.toReal_nonneg
  refine ⟨c * s * max B 1 ^ A * 2 ^ A, A, fun g hg h => ?_⟩
  have h1 : ∀ h', ‖thetaKO ω g h' f‖ ≤ (c * s * height V g ^ A) * height W h' ^ A := fun h' => by
    rw [mul_assoc _ (height V g ^ A), ← mul_pow]; exact key g h'
  refine (norm_le_quotHeight_pow (GlobalTheory.Chain.LiftConv.thetaKO_left hω hf g) h1 h).trans ?_
  have hg1 : height V g ^ A ≤ max B 1 ^ A :=
    pow_le_pow_left₀ (height_pos V g).le ((hB g hg).trans (le_max_left _ _)) A
  have hq := (pow_pos (quotHeight_pos W h) A).le
  have h2 : (0:ℝ) ≤ 2 ^ A := by positivity
  calc c * s * height V g ^ A * 2 ^ A * quotHeight W h ^ A
      ≤ c * s * max B 1 ^ A * 2 ^ A * quotHeight W h ^ A := by gcongr
    _ = _ := rfl

end GlobalTheory.CuspApproxX

namespace GlobalTheory.CuspApproxX

open GlobalTheory.Grow GlobalTheory.Size

end GlobalTheory.CuspApproxX

namespace GlobalTheory.CuspApproxX

end GlobalTheory.CuspApproxX

end
