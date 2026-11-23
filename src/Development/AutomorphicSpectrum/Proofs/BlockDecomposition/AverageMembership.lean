module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMirGen

theorem avgMem : AvgMem := by
  unfold AvgMem ForRep
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar _ _Γ P c _ φ hφ hLaw w
  haveI := hHaar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  change ∀ r : K, (r : G) ∈ P → c r • ρ r (avg μ ρ φ w) = avg μ ρ φ w
  intro r hr
  have hcont : Continuous fun κ : K => φ κ • ρ κ := hφ.smul hρ
  have hint : Integrable (fun κ : K => φ κ • ρ κ) μ :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have key : avg μ ρ φ = c r • (ρ r).comp (avg μ ρ φ) := by
    show ∫ κ, φ κ • ρ κ ∂μ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ)
    calc ∫ κ, φ κ • ρ κ ∂μ = ∫ κ, φ (r * κ) • ρ (r * κ) ∂μ :=
          (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) r).symm
      _ = ∫ κ, c r • (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := by
          congr 1
          funext κ
          rw [hLaw r κ hr, map_mul]
          ext x
          simp [mul_smul]
      _ = c r • ∫ κ, (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := integral_smul _ _
      _ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ) := by
          rw [(ContinuousLinearMap.compL ℂ W W W (ρ r)).integral_comp_comm hint]
          rfl
  have hw := congrArg (fun T : W →L[ℂ] W => T w) key
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply] at hw
  exact hw.symm

end GlobalTheory.CompanionTheory.EisMirGen
